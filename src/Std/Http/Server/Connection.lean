/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async.TCP
public import Std.Async.ContextAsync
public import Std.Http.Transport
public import Std.Http.Transport.Outbox
public import Std.Http.Protocol.H1
public import Std.Http.Server.Config
public import Std.Http.Server.Driver
public import Std.Http.Server.Handler

public section

namespace Std
namespace Http
namespace Server

open Std Async TCP Protocol
open Time
open Internal (Outbox)

/-!
# Connection

This module defines `Server.Connection`, a structure used to handle a single HTTP connection with
possibly multiple requests. The connection performs what `Server.Driver` decides: it runs the
driver's commands, waits on the sources the driver's state arms, and reports what happened, and the
time, as the driver's inputs.
-/

set_option linter.all true

/--
Represents the remote address of a client connection.
-/
structure RemoteAddr where
  /--
  The socket address of the remote client.
  -/
  addr : Net.SocketAddress
deriving TypeName

instance : ToString RemoteAddr where
  toString addr := toString addr.addr

/--
A single HTTP connection.
-/
structure Connection (α : Type) where
  /--
  The client connection.
  -/
  socket : α

  /--
  The processing machine for HTTP/1.1.
  -/
  machine : H1.Machine .receiving

  /--
  Extensions to attach to each request (e.g., remote address).
  -/
  extensions : Extensions := .empty

namespace Connection

/--
The I/O resources behind the sources the driver arms.
-/
private structure Live (β : Type) where
  /--
  Where the handlers' results arrive. One channel serves the whole connection: a handler is abandoned
  only when the connection ends, so a result that arrives is always the running handler's.
  -/
  responses : Std.Channel (Except IO.Error (Response β))
  /-- The handler that runs. -/
  handler : Option (AsyncTask (Response β)) := none
  /-- Where the asked `Expect: 100-continue` decision arrives. -/
  decision : Option (Std.Channel Bool) := none
  /-- The request body of the running exchange. -/
  requestBody : Option Body.Stream := none
  /-- The response body of the running exchange. -/
  responseBody : Option β := none
  /-- An input that is known without waiting, reported before anything else. -/
  ready : Option Driver.Input := none
  /-- The second, since the Unix epoch, that the machine's `Date` was formatted for. -/
  dateSecond : Option Int := none

/--
Calls `Handler.onFailure`, dropping any error it throws, so the connection's own handling and cleanup
still run.
-/
private def reportFailure {σ : Type} [Handler σ] (handler : σ) (error : IO.Error) : Async Unit :=
  try Handler.onFailure handler error catch _ => pure ()

/--
Keeps the machine's `Date` current when `Config.generateDate` is set, formatting it at most once per
second.
-/
private def refreshDate (config : Config) (s : Driver.State) (live : Live β) :
    IO (Driver.State × Live β) := do
  if !config.generateDate then
    return (s, live)
  let now ← Timestamp.now
  let second := now.toSecondsSinceUnixEpoch.val
  if live.dateSecond == some second then
    return (s, live)
  let date := Header.Value.ofString! (DateTime.ofTimestamp now TimeZone.ZoneRules.UTC).toHTTPDateString
  return (s.setDate (some date), { live with dateSecond := some second })

/--
Turns the handler's result into an input, keeping the response body to pull from. The body chunks
available at once go with the head, so a small response goes out in one write: one chunk, and the
end too for a body of known length, which cannot change its framing. Taking more could let a
producer close a body of unknown length before its head is written, which would give it a fixed
length.
-/
private def responded [Body β] (result : Except IO.Error (Response β)) (live : Live β) :
    Async (Driver.Input × Live β) := do
  match result with
  | .error err => return (.handlerFailed err, { live with handler := none })
  | .ok res =>
    let live := { live with handler := none, responseBody := some res.body }
    try
      let size ← Body.getKnownSize res.body
      match ← Body.tryRecv res.body with
      | none => return (.responded res.line size #[] false, live)
      | some none => return (.responded res.line size #[] true, live)
      | some (some chunk) =>
        if size matches some (.fixed _) then
          match ← Body.tryRecv res.body with
          | some none => return (.responded res.line size #[chunk] true, live)
          | _ => return (.responded res.line size #[chunk] false, live)
        else
          return (.responded res.line size #[chunk] false, live)
    catch err =>
      return (.responded res.line none #[] false, { live with ready := some (.failed err) })

/--
A selector for the end of `task`.
-/
private def taskSelector (task : Task α) : Selector α where
  tryFn := do
    if ← IO.hasFinished task then return some task.get else return none
  registerFn waiter :=
    BaseIO.chainTask (sync := true) task fun value =>
      waiter.race (pure ()) fun promise => promise.resolve (.ok value)
  unregisterFn := pure ()

/--
The input that reports the outbox's writes: `written`, or `writeFailed` with the first error.
-/
private def writesInput (outbox : Outbox α) : BaseIO Driver.Input := do
  if ← outbox.failed then
    return .writeFailed ((← outbox.takeError?).getD (.userError "write failed"))
  return .written

/--
Closes a connection's side gracefully (RFC 9112 §9.6). Closing a socket while the client is still
sending makes the kernel reset the connection, which can destroy the response before the client
reads it. So the write side is shut down first, then input is read and discarded until the client
closes its side, `timeout` passes or the server shuts down. Does nothing for a transport that cannot
shut down.
-/
private def linger [Transport α] (socket : α) (timeout : Millisecond.Offset) (readSize : UInt64)
    (connectionContext : CancellationContext) : Async Unit := do
  unless ← (try Transport.shutdown socket catch _ => pure false) do
    return
  let deadline := (← IO.monoMsNow) + timeout.toInt.toNat
  repeat
    let now ← IO.monoMsNow
    if now ≥ deadline then
      break
    let read ← try
        Selectable.one #[
          .case (Transport.recvSelector socket readSize) (fun data => pure (data.isSome)),
          .case connectionContext.doneSelector (fun _ => pure false),
          .case (← Selector.sleep (.ofNat (deadline - now))) (fun _ => pure false)]
      catch _ => pure false
    unless read do
      break

/--
Performs one command of the driver.
-/
private def perform
    {σ : Type} [Transport α] [Handler σ] [Body (Handler.ResponseBody σ)]
    (socket : α) (handler : σ) (config : Config) (extensions : Extensions)
    (connectionContext : CancellationContext) (outbox : Outbox α) (live : Live (Handler.ResponseBody σ)) :
    Driver.Command → Async (Live (Handler.ResponseBody σ))
  | .write data => do
    if (← outbox.send data).isNone then
      return { live with ready := some (← writesInput outbox) }
    return live
  | .startHandler line size complete => do
    let stream ← Body.mkStream
    Body.setKnownSize stream size
    if complete then
      Body.close stream
    let task ← Handler.onRequest handler { line, body := stream, extensions } connectionContext
      |>.asTask
    BaseIO.chainTask task (discard ∘ live.responses.send)
    return { live with requestBody := some stream, handler := some task }
  | .askContinue head => do
    let channel : Std.Channel Bool ← Std.Channel.new
    let task ← Handler.onContinue handler head |>.asTask
    BaseIO.chainTask task fun
      | .ok v => discard <| channel.send v
      | .error _ => discard <| channel.send false
    return { live with decision := some channel }
  | .pushBody chunk incomplete final => do
    if let some stream := live.requestBody then
      -- The reader that waited may have withdrawn since, for example a `recvSelector` that lost its
      -- select, so the chunk is offered rather than sent: the connection must not wait.
      try stream.offer chunk incomplete (closeAfter := final)
      catch e => reportFailure handler e
    return if final then { live with requestBody := none } else live
  | .failBody err => do
    if let some stream := live.requestBody then
      stream.closeWithError err
    return { live with requestBody := none }
  | .releaseResponse => do
    if let some body := live.responseBody then
      if !(← Body.isClosed body) then Body.close body
    return { live with responseBody := none }
  | .report err => do
    reportFailure handler err
    return live
  | .abandonHandler => do
    if let some task := live.handler then
      BaseIO.chainTask task fun
        | .ok res => discard <| EAsync.toBaseIO (ε := IO.Error) (Body.close res.body)
        | .error _ => pure ()
    return { live with handler := none }
  | .close lingerFirst => do
    if lingerFirst then
      linger socket config.lingeringTimeout config.maximumRecvSize.toUInt64 connectionContext
    Transport.close socket
    return live

/--
Waits for the next input: a source the driver's state arms, the outbox confirming the writes, the
driver's deadline, or the connection's cancellation.
-/
private def waitInput
    {σ : Type} [Transport α] [Handler σ] [Body (Handler.ResponseBody σ)]
    (cfg : Driver.Config) (socket : α) (connectionContext : CancellationContext) (outbox : Outbox α)
    (s : Driver.State) (live : Live (Handler.ResponseBody σ)) :
    Async (Driver.Input × Live (Handler.ResponseBody σ)) := do
  if let some input := live.ready then
    return (input, { live with ready := none })

  if s.watchesWrites then
    if ← outbox.failed then
      return (← writesInput outbox, live)

  let now ← IO.monoMsNow
  let deadline := Driver.nextDeadline s
  if let some (kind, time) := deadline then
    if time ≤ now then
      return (.deadline kind, live)

  -- A response chunk that is already there is taken without a select.
  let pullsResponse := Driver.pullsResponse cfg s
  if pullsResponse then
    if let some body := live.responseBody then
      try
        match ← Body.tryRecv body with
        | some (some chunk) => return (.responseData chunk, live)
        | some none => return (.responseEnd, live)
        | none => pure ()
      catch err => return (.responseFailed err, live)

  -- So is the interest of a request body reader that already waits.
  if Driver.wantsBodyInterest s then
    if let some stream := live.requestBody then
      if let some wanted ← stream.interestSelector.tryFn then
        return (if wanted then .bodyWanted else .bodyDropped, live)

  let mut selectables : Array (Selectable (Driver.Input × Live (Handler.ResponseBody σ))) := #[]

  if s.watchesWrites then
    match ← outbox.idle? with
    | none => return (← writesInput outbox, live)
    | some idle =>
      selectables := selectables.push (.case (taskSelector idle) fun _ => return (← writesInput outbox, live))

  let serving := s.phase == .serving

  if serving && !s.cancelled then
    selectables := selectables.push (.case connectionContext.doneSelector fun _ => do
      match ← connectionContext.getCancellationReason with
      | some .deadline => return (.timedOut, live)
      | _ => return (.shutdown, live))

  if Driver.wantsBytes cfg s then
    selectables := selectables.push (.case (Transport.recvSelector socket (Driver.recvSize cfg s).toUInt64) fun
      | some data => return (.received data, live)
      | none => return (.eof, live))

  if serving && s.handlerRunning then
    selectables := selectables.push (.case live.responses.recvSelector fun result => responded result live)

  if serving && s.asksContinue then
    if let some channel := live.decision then
      selectables := selectables.push (.case channel.recvSelector fun accept =>
        return (.continueDecided accept, { live with decision := none }))

  if Driver.wantsBodyInterest s then
    if let some stream := live.requestBody then
      selectables := selectables.push (.case stream.interestSelector fun
        | true => return (.bodyWanted, live)
        | false => return (.bodyDropped, live))

  if pullsResponse then
    if let some body := live.responseBody then
      selectables := selectables.push (.case (Body.recvSelector body) fun
        | some chunk => return (.responseData chunk, live)
        | none => return (.responseEnd, live))

  -- A source that is ready is taken before a timer is started for the deadline.
  let mut ready := none
  try
    unless selectables.isEmpty do ready ← Selectable.tryOne selectables
  catch err => return (.failed err, live)
  if let some input := ready then
    return input

  if let some (kind, time) := deadline then
    let sleep ← Selector.sleep ((time - now) * (1 : Millisecond.Offset))
    selectables := selectables.push (.case sleep fun _ => return (.deadline kind, live))

  if selectables.isEmpty then
    return (.failed (.userError "the connection waits for nothing"), live)

  try Selectable.one selectables
  catch err => return (.failed err, live)

/--
Runs the connection: performs the driver's commands and reports what happened as its next input,
until the driver closes the connection.
-/
private def handle
    {σ : Type} [Transport α] [h : Handler σ]
    (connection : Connection α)
    (config : Config)
    (connectionContext : CancellationContext)
    (handler : σ) : Async Unit := do

  let _ : Body (Handler.ResponseBody σ) := Handler.responseBodyInstance

  let socket := connection.socket
  let cfg := Driver.Config.ofServer config
  let outbox ← Outbox.new socket cfg.writeTimeout

  let mut live : Live (Handler.ResponseBody σ) := { responses := ← Std.Channel.new }
  let mut s := Driver.State.init connection.machine
  let mut input := Driver.Input.resume

  try
    repeat
      let (s', l) ← refreshDate config s live
      let (s'', cmds) := Driver.step cfg s' (← IO.monoMsNow) input
      s := s''
      live := l
      for cmd in cmds do
        live ← perform socket handler config connection.extensions connectionContext outbox live cmd
      if s.isClosed then
        break
      let (i, l) ← waitInput cfg socket connectionContext outbox s live
      input := i
      live := l
  catch err =>
    reportFailure handler err
    Transport.close socket

end Connection

/--
Handles request/response processing for a single connection using an `Async` handler.
The library-level entry point for running a server is `Server.serve`.
This function can be used with a `TCP.Socket` or any other type that implements
`Transport` to build custom server loops.

# Example

```lean
-- Create a TCP socket server instance
let server ← Socket.Server.mk
server.bind addr
server.listen backlog

-- Enter an infinite loop to handle incoming client connections
while true do
  let client ← server.accept
  background (serveConnection client handler config)
```
-/
def serveConnection
    {σ : Type} [Transport t] [Handler σ]
    (client : t) (handler : σ)
    (config : Config) (extensions : Extensions := .empty) : ContextAsync Unit := do
  (Connection.mk client { config := config.toH1Config } extensions)
  |>.handle config (← ContextAsync.getContext) handler

end Std.Http.Server
