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
import Std.Async.Watchdog

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
possibly multiple requests. Every decision of the connection is `Server.Driver`'s; this module performs
its commands, waits where it says, and reports what happened back to it.
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
What ends a wait.
-/
private inductive Woke (β : Type) where
  /-- An input for the driver. -/
  | input (input : Driver.Input)
  /-- The handler's response, or its failure. -/
  | response (result : Except IO.Error (Response β))
  /-- The write in flight runs late while the keep-alive timeout waits for it. -/
  | writeDue
  /-- The connection's context was cancelled. -/
  | cancelled

/--
What a connection keeps for its whole life.
-/
private structure Env (σ α : Type) where
  handler : σ
  config : Config
  extensions : Extensions
  socket : α
  /-- Where the driver's output is written. -/
  outbox : Outbox α
  /-- Lingering watches the server's context, so that a connection that timed out still lingers. -/
  serverContext : CancellationContext
  /-- Handed to the handlers; cancelled by `wd`, by the server, or when the connection ends. -/
  connectionContext : CancellationContext
  /-- Times the waits the driver arms, by cancelling `connectionContext`. -/
  wd : Watchdog

/--
The resources behind the driver's state.
-/
private structure Live (β : Type) where
  /-- The body of the current request, handed to its handler. -/
  requestStream : Body.Stream
  /-- Where the current handler's response arrives. -/
  response : Std.Channel (Except IO.Error (Response β))
  /-- The response body being written. -/
  responseBody : Option β := none
  /-- The handler whose response has not arrived, whether or not it is still waited for. -/
  handlerTask : Option (Task (Except IO.Error (Response β))) := none
  /-- Where the `Expect: 100-continue` decision arrives. -/
  continueAnswer : Option (Std.Channel Bool) := none

/--
Calls `Handler.onFailure`, dropping any error it throws, so the connection's own handling and cleanup
still run.
-/
private def reportFailure {σ : Type} [Handler σ] (handler : σ) (error : IO.Error) : Async Unit :=
  try Handler.onFailure handler error catch _ => pure ()

/--
Reports a failed write of `outbox` to the handler, once.
-/
private def reportWriteFailure [Handler σ] (handler : σ) (outbox : Outbox α) : Async Unit := do
  if let some err ← outbox.takeError? then
    reportFailure handler err

/--
Ends `stream`: cleanly when no body bytes are left undelivered, and otherwise with an error saying
`reason`. A final chunk already offered keeps its clean end, since `Stream.closeWithError` leaves it
alone.
-/
private def endRequestStream (stream : Body.Stream) (reason : String) : Async Unit := do
  if ← stream.isClosed then
    return
  if (← stream.getKnownSize) == some (.fixed 0) then
    stream.close
  else
    stream.closeWithError (.userError reason)

/--
Closes a connection's side gracefully (RFC 9112 §9.6): the write side is shut down first, then input
is read and discarded until the client closes its side, `timeout` passes or the server shuts down.
Does nothing for a transport that cannot shut down.
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
Performs one command. Returns whether it wrote, for a write command.
-/
private def perform
    {σ : Type} [Transport α] [Handler σ] [Body (Handler.ResponseBody σ)]
    (env : Env σ α) (live : Live (Handler.ResponseBody σ)) :
    Driver.Command → Async (Live (Handler.ResponseBody σ) × Option Bool)
  | .write data => written (env.outbox.push data)
  | .awaitWritten => written env.outbox.awaitWritten
  | .flush => written do env.outbox.awaitIdle; return !(← env.outbox.failed)
  | .startHandler line => do
    let task ← Handler.onRequest env.handler
      { line, body := live.requestStream, extensions := env.extensions } env.connectionContext
      |>.asTask
    BaseIO.chainTask task (discard ∘ live.response.send)
    return ({ live with handlerTask := some task }, none)
  | .askContinue head => do
    let answer : Std.Channel Bool ← Std.Channel.new
    let task ← Handler.onContinue env.handler head |>.asTask
    BaseIO.chainTask task fun
      | .ok accept => discard <| answer.send accept
      | .error _ => discard <| answer.send false
    return ({ live with continueAnswer := some answer }, none)
  | .setBodySize size => do
    Body.setKnownSize live.requestStream (some size)
    return (live, none)
  | .offerBody chunk incomplete final => do
    try live.requestStream.offer chunk incomplete (closeAfter := final)
    catch e => reportFailure env.handler e
    return (live, none)
  | .endBody reason => do
    endRequestStream live.requestStream reason
    return (live, none)
  | .nextExchange =>
    return ({ live with requestStream := ← Body.mkStream, response := ← Std.Channel.new }, none)
  | .closeResponse => do
    if let some body := live.responseBody then
      if ¬(← Body.isClosed body) then Body.close body
    return ({ live with responseBody := none }, none)
  | .releaseHandler => do
    if let some task := live.handlerTask then
      background do
        if let .ok res ← Async.ofTask task then
          Body.close res.body
    return (live, none)
  | .report err => do
    reportFailure env.handler err
    return (live, none)
  | .close lingerFirst => do
    if lingerFirst then
      linger env.socket env.config.lingeringTimeout env.config.maximumRecvSize.toUInt64
        env.serverContext
    return (live, none)
where
  /-- Runs a write, reporting its failure once. -/
  written (write : Async Bool) : Async (Live (Handler.ResponseBody σ) × Option Bool) := do
    let ok ← write
    unless ok do reportWriteFailure env.handler env.outbox
    return (live, some ok)

/--
Performs `cmds` in order, stopping at a write that fails. Returns whether the writes succeeded, if
there were any.
-/
private def performAll
    {σ : Type} [Transport α] [Handler σ] [Body (Handler.ResponseBody σ)]
    (env : Env σ α) (live : Live (Handler.ResponseBody σ)) (cmds : Array Driver.Command) :
    Async (Live (Handler.ResponseBody σ) × Option Bool) := do
  let mut live := live
  let mut written := none
  for cmd in cmds do
    let (l, ok?) ← perform env live cmd
    live := l
    if let some ok := ok? then
      written := some ok
      unless ok do break
  return (live, written)

/--
Arms the watchdog for a wait. Returns when the write in flight runs late, for an `afterWrites` wait
whose writes are still in flight, so the loop can wake for it.
-/
private def arm (wd : Watchdog) (outbox : Outbox α) : Driver.Arm → BaseIO (Option Nat)
  | .until deadline => do
    wd.armUntil deadline
    return none
  | .within timeout => do
    wd.arm timeout
    return none
  | .afterWrites timeout => do
    if let some idle ← outbox.idle? then
      wd.armAfter idle timeout
      outbox.writeDeadline?
    else
      wd.arm timeout
      return none

/--
Waits on `sources` under their timer, with the write in flight's deadline `writeDue`.
-/
private def poll
    {σ β : Type} [Transport α] [Handler σ] [Body β]
    (env : Env σ α) (live : Live β) (sources : Driver.Sources) (writeDue : Option Nat) :
    Async (Woke β) := do
  let mut selectables : Array (Selectable (Woke β)) :=
    #[.case env.connectionContext.doneSelector fun _ => pure .cancelled]
  if let some size := sources.recv then
    selectables := selectables.push
      (.case (Transport.recvSelector env.socket size.toUInt64) (pure ∘ .input ∘ .received))
  if let some due := writeDue then
    let wait := Millisecond.Offset.ofNat (due - (← IO.monoMsNow))
    selectables := selectables.push (.case (← Selector.sleep wait) fun _ => pure .writeDue)
  if sources.responseBody then
    if let some body := live.responseBody then
      selectables := selectables.push (.case (Body.recvSelector body) (pure ∘ .input ∘ .pulled))
  if sources.requestBody then
    selectables := selectables.push
      (.case live.requestStream.interestSelector (pure ∘ .input ∘ .bodyInterest))
  if sources.response then
    selectables := selectables.push (.case live.response.recvSelector (pure ∘ .response))
  try Selectable.one selectables
  catch e =>
    reportFailure env.handler e
    pure (.input .failed)

/--
Turns the handler's response into the driver's input. A response the driver writes the body of has
one chunk taken at once if it is there, so a body already in memory, such as `Body.Full`, needs no
further wait; only one, since a producer could otherwise close a body of unknown length before its
head is written, giving it a fixed length.
-/
private def responded [Body β] (s : Driver.State) (live : Live β) (res : Response β) :
    Async (Driver.Input × Live β) := do
  let live := { live with handlerTask := none, responseBody := some res.body }
  let size ← Body.getKnownSize res.body
  if !Driver.writesBody s res.line size then
    return (.responded res.line size (.ok none), live)
  try
    let first ← Body.tryRecv res.body
    if first matches some none then
      if ¬(← Body.isClosed res.body) then Body.close res.body
      return (.responded res.line size (.ok first), { live with responseBody := none })
    return (.responded res.line size (.ok first), live)
  catch e => return (.responded res.line size (.error e), live)

/--
Turns what ended a wait into the driver's input.
-/
private def toInput
    {σ : Type} [Handler σ] [Body (Handler.ResponseBody σ)]
    (env : Env σ α) (s : Driver.State) (live : Live (Handler.ResponseBody σ)) :
    Woke (Handler.ResponseBody σ) → Async (Driver.Input × Live (Handler.ResponseBody σ))
  | .input input => return (input, live)
  | .writeDue => do
    -- The keep-alive timeout starts once the last response is written, so wait for that write
    -- under the write timeout, which fails the outbox if the peer stopped reading.
    env.outbox.awaitIdle
    return (.resume, live)
  | .cancelled => do
    let deadline := (← env.connectionContext.getCancellationReason) matches some .deadline
    return (.cancelled (← env.wd.hasFired) deadline, live)
  | .response (.error err) => return (.handlerFailed err, { live with handlerTask := none })
  | .response (.ok res) => responded s live res

/--
Waits for the `Expect: 100-continue` decision. Cancellation and `lingeringTimeout` reject it.
-/
private def waitContinue (env : Env σ α) (live : Live β) : Async (Driver.Input × Live β) := do
  let some answer := live.continueAnswer | return (.continueDecided false, live)
  let accept ← Selectable.one #[
    .case answer.recvSelector pure,
    .case env.connectionContext.doneSelector (fun _ => pure false),
    .case (← Selector.sleep env.config.lingeringTimeout) (fun _ => pure false)
  ]
  return (.continueDecided accept, { live with continueAnswer := none })

/--
Waits for the next input. A timer that passed while another source won is reported instead of that
source.
-/
private def wait
    {σ : Type} [Transport α] [Handler σ] [Body (Handler.ResponseBody σ)]
    (env : Env σ α) (s : Driver.State) (live : Live (Handler.ResponseBody σ)) :
    Async (Driver.Input × Live (Handler.ResponseBody σ)) := do
  if s.asksContinue then
    return ← waitContinue env live

  let (bodyOpen, bodyInterested) ←
    if s.readsBodyState then
      let bodyOpen := !(← Body.isClosed live.requestStream)
      pure (bodyOpen, ← if bodyOpen then live.requestStream.hasInterest else pure false)
    else pure (false, false)
  let sources := Driver.sources env.config s bodyOpen bodyInterested
  let writeDue ←
    match sources.timer with
    | some timer => arm env.wd env.outbox timer
    | none => pure none
  let woke ← poll env live sources writeDue
  if ← env.wd.disarm then
    if let .response (.ok res) := woke then
      if ¬(← Body.isClosed res.body) then Body.close res.body
    return (.cancelled true false, live)
  toInput env s live woke

/--
Runs a single connection: performs the driver's commands, and feeds it what happened until it closes.

`wd` enforces the connection's timeouts by cancelling `connectionContext`. Lingering watches
`serverContext` instead, so that a connection that timed out still lingers after its 408.
-/
private def run
    {σ : Type} [Transport α] [h : Handler σ]
    (connection : Connection α)
    (config : Config)
    (serverContext connectionContext : CancellationContext)
    (wd : Watchdog)
    (handler : σ) : Async Unit := do
  let _ : Body (Handler.ResponseBody σ) := Handler.responseBodyInstance
  let env : Env σ α := {
    handler, config, serverContext, connectionContext, wd
    extensions := connection.extensions
    socket := connection.socket
    outbox := ← Outbox.new connection.socket config.writeTimeout.toInt.toNat
  }
  let mut live : Live (Handler.ResponseBody σ) :=
    { requestStream := ← Body.mkStream, response := ← Std.Channel.new }
  let mut s := Driver.init connection.machine
  let mut input := Driver.Input.resume
  try
    repeat
      let (s', cmds) := Driver.step config s (← IO.monoMsNow) input (some (← Timestamp.now))
      s := s'
      let (l, written) ← performAll env live cmds
      live := l
      if s.isClosed then
        break
      match written with
      | some ok => input := .written ok
      | none =>
        if s.waits then
          let (i, l) ← wait env s live
          input := i
          live := l
        else
          input := .resume
  finally
    Transport.close connection.socket

/--
Serves a single connection under a child of `serverContext`, whose watchdog enforces the
connection's timeouts.
-/
private def handle
    {σ : Type} [Transport α] [Handler σ]
    (connection : Connection α)
    (config : Config)
    (serverContext : CancellationContext)
    (handler : σ) : Async Unit := do
  -- A child context, so that a timeout cancels only this connection.
  let connectionContext ← serverContext.fork
  let wd ← Watchdog.new connectionContext
  -- Cancelling the context once the connection ends also stops the watchdog.
  try run connection config serverContext connectionContext wd handler
  finally connectionContext.cancel .cancel

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
