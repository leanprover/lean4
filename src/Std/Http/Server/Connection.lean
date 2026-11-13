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

This module serves a single HTTP connection with possibly multiple requests (`serveConnection`). The
connection performs what `Server.Driver` decides: it runs the driver's commands, waits on the
sources the driver's state arms, and reports what happened, and the time, as the driver's inputs.
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

namespace Connection

/--
The result of a handler, or of an `Expect: 100-continue` decision. A connection runs at most one of
them at a time, so one channel carries both.
-/
private inductive Answer (β : Type) where
  /--
  The handler's response, or its failure.
  -/
  | response (result : Except IO.Error (Response β))

  /--
  The decision on `Expect: 100-continue`.
  -/
  | decision (accept : Bool)

/--
What ends a wait. The continuations of a wait's cases capture nothing, so they allocate nothing; what
needs the connection's state is done once the wait is over (`wake`).
-/
private inductive Woke (β : Type) where
  /--
  An input for the driver.
  -/
  | input (input : Driver.Input)

  /--
  The writes in flight completed or failed.
  -/
  | writes

  /--
  The connection's context was cancelled.
  -/
  | cancelled

  /--
  A handler or an `Expect: 100-continue` decision answered; `none` once the channel is closed.
  -/
  | answer (answer : Option (Answer β))

/--
What a connection keeps for its whole life.
-/
private structure Env (σ α β : Type) where
  /--
  The transport.
  -/
  socket : α

  /--
  The handler.
  -/
  handler : σ

  /--
  The server configuration.
  -/
  config : Config

  /--
  Extensions to attach to each request (e.g., remote address).
  -/
  extensions : Extensions

  /--
  The connection's cancellation context.
  -/
  context : CancellationContext

  /--
  Where the output goes.
  -/
  outbox : Outbox α

  /--
  Where the handlers' results and the `Expect: 100-continue` decisions arrive. A handler is abandoned
  only when the connection ends, so a result that arrives is always the running handler's.
  -/
  answers : Std.CloseableChannel (Answer β)

  /--
  The connection's cancellation, as a case of a wait.
  -/
  cancelCase : Selectable (Woke β)

  /--
  An answer on `answers`, as a case of a wait.
  -/
  answerCase : Selectable (Woke β)

/--
The I/O resources behind the sources the driver arms.
-/
private structure Live (β : Type) where
  /--
  The handler that runs.
  -/
  handler : Option (AsyncTask (Response β)) := none

  /--
  The request body of the running exchange.
  -/
  requestBody : Option Body.Stream := none

  /--
  The response body of the running exchange.
  -/
  responseBody : Option β := none

  /--
  An input that is known without waiting, reported before anything else.
  -/
  ready : Option Driver.Input := none

  /--
  Until when, by `IO.monoMsNow`, the machine's `Date` stays current: the end of the second it was
  formatted for.
  -/
  dateUntil : Nat := 0

  /--
  The last write completion reported to the driver (`Outbox.completedAt`).
  -/
  completedSeen : Nat := 0

/--
Calls `Handler.onFailure`, dropping any error it throws, so the connection's own handling and
cleanup still run.
-/
private def reportFailure {σ : Type} [Handler σ] (handler : σ) (error : IO.Error) : Async Unit :=
  try Handler.onFailure handler error catch _ => pure ()

/--
Keeps the machine's `Date` current when `Config.generateDate` is set. The wall clock is read, and the
field formatted, only once the second it was formatted for is over.
-/
private def refreshDate (config : Config) (now : Nat) (s : Driver.State) (live : Live β) :
    IO (Driver.State × Live β) := do
  if !config.generateDate || now < live.dateUntil then
    return (s, live)
  let wall ← Timestamp.now
  let intoSecond := (wall.toMillisecondsSinceUnixEpoch.val % 1000).toNat
  let date :=
    Header.Value.ofString! (DateTime.ofTimestamp wall TimeZone.ZoneRules.UTC).toHTTPDateString
  return (s.setDate (some date), { live with dateUntil := now + (1000 - intoSecond) })

/--
Turns the handler's result into an input, keeping the response body to pull from. The body chunks
available at once go with the head, so a small response goes out in one write: one chunk, and for a
body of known length, which cannot change its framing, the next chunk or the end. Taking more could
let a producer close a body of unknown length before its head is written, which would give it a
fixed length.
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
          | some (some next) => return (.responded res.line size #[chunk, next] false, live)
          | none => return (.responded res.line size #[chunk] false, live)
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
The input that reports the outbox's writes: `written`, or `writeFailed` with the error.
-/
private def writesInput (outbox : Outbox α) : BaseIO Driver.Input := do
  match ← outbox.error? with
  | some err => return .writeFailed err
  | none => return .written

/--
The input for a deadline of kind `kind` that passed. Only the outbox knows when a write last
completed, so a completion the driver has not heard of is reported first, as `writeProgress`, which
restarts the write deadline.
-/
private def deadlineInput (outbox : Outbox α) (live : Live β) :
    Driver.Deadline → BaseIO (Driver.Input × Live β)
  | .write => do
    let completedAt ← outbox.completedAt
    if completedAt > live.completedSeen then
      return (.writeProgress completedAt, { live with completedSeen := completedAt })
    return (.deadline .write, live)
  | kind => return (.deadline kind, live)

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
    (env : Env σ α (Handler.ResponseBody σ)) (live : Live (Handler.ResponseBody σ)) :
    Driver.Command → Async (Live (Handler.ResponseBody σ))
  | .write data => do
    env.outbox.send data
    return live
  | .startHandler line size complete => do
    let stream ← Body.mkStream
    Body.setKnownSize stream size
    if complete then
      Body.close stream
    let task ← Handler.onRequest env.handler { line, body := stream, extensions := env.extensions }
      env.context |>.asTask
    BaseIO.chainTask (sync := true) task fun result =>
      discard <| env.answers.trySend (.response result)
    return { live with requestBody := some stream, handler := some task }
  | .askContinue head => do
    let task ← Handler.onContinue env.handler head |>.asTask
    BaseIO.chainTask (sync := true) task fun result =>
      discard <| env.answers.trySend (.decision (match result with | .ok accept => accept | _ => false))
    return live
  | .pushBody chunk incomplete final => do
    if let some stream := live.requestBody then
      -- The reader that waited may have withdrawn since, for example a `recvSelector` that lost its
      -- select, so the chunk is offered rather than sent: the connection must not wait.
      try stream.offer chunk incomplete (closeAfter := final)
      catch e => reportFailure env.handler e
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
    reportFailure env.handler err
    return live
  | .abandonHandler => do
    if let some task := live.handler then
      BaseIO.chainTask task fun
        | .ok res => discard <| EAsync.toBaseIO (ε := IO.Error) (Body.close res.body)
        | .error _ => pure ()
    return { live with handler := none }
  | .close lingerFirst => do
    if lingerFirst then
      linger env.socket env.config.lingeringTimeout env.config.maximumRecvSize.toUInt64 env.context
    Transport.close env.socket
    return live

/--
Turns what ended a wait into the driver's input.
-/
private def wake
    {σ : Type} [Handler σ] [Body (Handler.ResponseBody σ)]
    (env : Env σ α (Handler.ResponseBody σ)) (live : Live (Handler.ResponseBody σ)) :
    Woke (Handler.ResponseBody σ) → Async (Driver.Input × Live (Handler.ResponseBody σ))
  | .input (.deadline kind) => return (← deadlineInput env.outbox live kind)
  | .input input => return (input, live)
  | .writes => return (← writesInput env.outbox, live)
  | .cancelled => do
    let reason ← env.context.getCancellationReason
    return (.cancelled (reason matches some .deadline), live)
  | .answer (some (.response result)) => responded result live
  | .answer (some (.decision accept)) => return (.continueDecided accept, live)
  | .answer none => return (.failed (.userError "the connection's answers were closed"), live)

/--
Waits for the next input: the outbox confirming the writes, the driver's deadline, a source the
driver's state arms, or the connection's cancellation.
-/
private def waitInput
    {σ : Type} [Transport α] [Handler σ] [Body (Handler.ResponseBody σ)]
    (env : Env σ α (Handler.ResponseBody σ)) (s : Driver.State)
    (live : Live (Handler.ResponseBody σ)) :
    Async (Driver.Input × Live (Handler.ResponseBody σ)) := do
  if let some input := live.ready then
    return (input, { live with ready := none })

  let mut writes := none
  if s.watchesWrites then
    match ← env.outbox.idle? with
    | none => return (← writesInput env.outbox, live)
    | some idle => writes := some idle

  let now ← IO.monoMsNow
  let deadline := Driver.nextDeadline s
  if let some (kind, time) := deadline then
    if time ≤ now then
      return (← deadlineInput env.outbox live kind)

  -- A response chunk that is already there is taken without a select.
  let pullsResponse := Driver.pullsResponse s
  if pullsResponse then
    if let some body := live.responseBody then
      try
        if let some chunk ← Body.tryRecv body then
          return (.pulled chunk, live)
      catch err => return (.failed err, live)

  -- So is the interest of a request body reader that already waits.
  let wantsBodyInterest := Driver.wantsBodyInterest s
  if wantsBodyInterest then
    if let some stream := live.requestBody then
      if let some wanted ← stream.interestSelector.tryFn then
        return (.bodyInterest wanted, live)

  let mut selectables : Array (Selectable (Woke (Handler.ResponseBody σ))) := #[]

  if let some idle := writes then
    selectables := selectables.push (.case (taskSelector idle) fun _ => pure .writes)

  if s.phase == .serving && !s.cancelled then
    selectables := selectables.push env.cancelCase

  if Driver.wantsBytes env.config s then
    let recv := Transport.recvSelector env.socket (Driver.recvSize env.config s).toUInt64
    selectables := selectables.push (.case recv fun data => pure (.input (.received data)))

  if s.handlerRunning || s.asksContinue then
    selectables := selectables.push env.answerCase

  if wantsBodyInterest then
    if let some stream := live.requestBody then
      selectables := selectables.push
        (.case stream.interestSelector fun wanted => pure (.input (.bodyInterest wanted)))

  if pullsResponse then
    if let some body := live.responseBody then
      selectables := selectables.push
        (.case (Body.recvSelector body) fun chunk => pure (.input (.pulled chunk)))

  -- A source that is ready is taken before a timer is started for the deadline.
  try
    unless selectables.isEmpty do
      if let some woke ← Selectable.tryOne selectables then
        return ← wake env live woke
  catch err => return (.failed err, live)

  if let some (kind, time) := deadline then
    let sleep ← Selector.sleep ((time - now) * (1 : Millisecond.Offset))
    selectables := selectables.push (.case sleep fun _ => pure (.input (.deadline kind)))

  if selectables.isEmpty then
    return (.failed (.userError "the connection waits for nothing"), live)

  try wake env live (← Selectable.one selectables)
  catch err => return (.failed err, live)

/--
Runs the connection: performs the driver's commands and reports what happened as its next input,
until the driver closes the connection.
-/
private def handle
    {σ : Type} [Transport α] [h : Handler σ]
    (socket : α)
    (extensions : Extensions)
    (config : Config)
    (connectionContext : CancellationContext)
    (handler : σ) : Async Unit := do

  let _ : Body (Handler.ResponseBody σ) := Handler.responseBodyInstance

  let answers ← Std.CloseableChannel.new
  let env : Env σ α (Handler.ResponseBody σ) := {
    socket, handler, config, extensions, context := connectionContext, answers
    outbox := ← Outbox.new socket
    cancelCase := .case connectionContext.doneSelector fun _ => pure .cancelled
    answerCase := .case answers.recvSelector fun answer => pure (.answer answer) }

  let mut live : Live (Handler.ResponseBody σ) := {}
  let mut s := Driver.State.init { config := config.toH1Config }
  let mut input := Driver.Input.resume

  try
    repeat
      let now ← IO.monoMsNow
      let (s', l) ← refreshDate config now s live
      let (s'', cmds) := Driver.step config s' now input
      s := s''
      live := l
      for cmd in cmds do
        live ← perform env live cmd
      if s.isClosed then
        break
      let (i, l) ← waitInput env s live
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
  Connection.handle client extensions config (← ContextAsync.getContext) handler

end Std.Http.Server
