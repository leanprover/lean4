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
possibly multiple requests.
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
Events produced by the async select loop in `receiveWithTimeout`.
Each variant corresponds to one possible outcome of waiting for I/O.
-/
private inductive Recv (β : Type)
  | bytes (x : Option ByteArray)
  | responseBody (x : Option Chunk)
  | bodyInterest (x : Bool)
  | response (x : (Except IO.Error (Response β)))
  | timeout
  | keepAliveTimeout
  | shutdown
  | close

/--
The set of I/O sources to wait on during a single poll iteration.
Each `Option` field is `none` when that source is not currently active.
-/
private structure PollSources (α β : Type) where
  socket : Option α
  expect : Option Nat
  response : Option (Std.Channel (Except IO.Error (Response β)))
  responseBody : Option β
  requestBody : Option Body.Stream
  timeout : Millisecond.Offset
  keepAliveTimeout : Option Millisecond.Offset
  headerTimeout : Option Timestamp
  connectionContext : CancellationContext

/--
Waits for the next I/O event across all active sources described by `sources`.
Computes the socket recv size from `config`, then races all active selectables.
Calls `Handler.onFailure` and returns `.close` on transport errors.
-/
private def pollNextEvent
    {σ β : Type} [Transport α] [Handler σ] [Body β]
    (config : Config) (handler : σ) (sources : PollSources α β)
    : Async (Recv β) := do
  let expectedBytes := sources.expect
    |>.getD config.defaultPayloadBytes
    |>.min config.maximumRecvSize
    |>.toUInt64

  let mut selectables : Array (Selectable (Recv β)) := #[
    .case sources.connectionContext.doneSelector (fun _ => do
      let reason ← sources.connectionContext.getCancellationReason
      match reason with
      | some .deadline => pure .timeout
      | _ => pure .shutdown)
  ]

  if let some socket := sources.socket then
    selectables := selectables.push (.case (Transport.recvSelector socket expectedBytes) (Recv.bytes · |> pure))


    if sources.keepAliveTimeout.isNone then
      if let some timeout := sources.headerTimeout then
        selectables := selectables.push (.case (← Selector.sleep (timeout - (← Timestamp.now)).toMilliseconds) (fun _ => pure .timeout))
      else
        selectables := selectables.push (.case (← Selector.sleep sources.timeout) (fun _ => pure .timeout))
    else
      selectables := selectables.push (.case (← Selector.sleep sources.timeout) (fun _ => pure .keepAliveTimeout))

  if let some responseBody := sources.responseBody then
    selectables := selectables.push (.case (Body.recvSelector responseBody) (Recv.responseBody · |> pure))

  if let some requestBody := sources.requestBody then
    selectables := selectables.push (.case (requestBody.interestSelector) (Recv.bodyInterest · |> pure))

  if let some response := sources.response then
    selectables := selectables.push (.case response.recvSelector (Recv.response · |> pure))

  try Selectable.one selectables
  catch e =>
    Handler.onFailure handler e
    pure .close

/--
Handles the `Expect: 100-continue` protocol for a pending request head.
Races between the handler's decision (`Handler.onContinue`), the connection being
cancelled, and a lingering timeout. Returns the updated machine and whether
`pendingHead` should be cleared (i.e. when the request is rejected).
-/
private def handleContinueEvent
    {σ : Type} [Handler σ]
    (handler : σ) (machine : H1.Machine .receiving) (head : Request.Head)
    (config : Config) (connectionContext : CancellationContext)
    : Async (H1.Machine .receiving × Bool) := do

  let continueChannel : Std.Channel Bool ← Std.Channel.new
  let continueTask ← Handler.onContinue handler head |>.asTask

  BaseIO.chainTask continueTask fun
    | .ok v => discard <| continueChannel.send v
    | .error _ => discard <| continueChannel.send false

  let canContinue ← Selectable.one #[
    .case continueChannel.recvSelector pure,
    .case connectionContext.doneSelector (fun _ => pure false),
    .case (← Selector.sleep config.lingeringTimeout) (fun _ => pure false)
  ]

  let status := if canContinue then Status.«continue» else Status.expectationFailed
  return (machine.canContinue status, !canContinue)

/--
Applies a successful handler response to the machine.
Records the known body size and sends the response head. Returns the updated machine and the body
stream to drain, or `none` when the body should be omitted (e.g., for HEAD requests).
-/
private def applyResponse
    {β : Type} [Body β]
    (machine : H1.Machine .receiving) (res : Response β)
    : Async (H1.Machine .receiving × Option β) := do
  let size ← Body.getKnownSize res.body

  let machineSized :=
    if let some knownSize := size
      then machine.setKnownSize knownSize
      else machine

  let machineWithHead := machineSized.send res.line
  if machineWithHead.writer.omitBody then
    if ¬(← Body.isClosed res.body) then
      Body.close res.body
    return (machineWithHead, none)
  else
    return (machineWithHead, some res.body)

/--
All mutable state carried through the connection processing loop.
Bundled into a struct so it can be passed to and returned from helper functions.
-/
private structure ConnectionState (β : Type) where
  machine : H1.Machine .receiving
  requestStream : Body.Stream
  keepAliveTimeout : Option Millisecond.Offset
  currentTimeout : Millisecond.Offset
  headerTimeout : Option Timestamp
  response : Std.Channel (Except IO.Error (Response β))
  respStream : Option β
  requiresData : Bool
  expectData : Option Nat
  handlerDispatched : Bool
  pendingHead : Option Request.Head
  /-- The second, since the Unix epoch, that `machine.date` was formatted for. -/
  dateSecond : Option Int := none

/--
Keeps `machine.date` current when `Config.generateDate` is set, formatting it at most once per
second. The machine writes response heads during `Machine.step`, and the 500 for a head it rejects
in `Machine.send`, so this runs before each step and before a response is applied.
-/
private def refreshDate (config : Config) (state : ConnectionState β) : IO (ConnectionState β) := do
  if !config.generateDate then
    return state
  let now ← Timestamp.now
  let second := now.toSecondsSinceUnixEpoch.val
  if state.dateSecond == some second then
    return state
  let date := Header.Value.ofString! (DateTime.ofTimestamp now TimeZone.ZoneRules.UTC).toHTTPDateString
  return { state with machine := { state.machine with date := some date }, dateSecond := some second }

/--
Processes all H1 events from a single machine step, updating the connection state.
Handles keep-alive resets, body-size tracking, `Expect: 100-continue`, and parse errors.
Returns the updated state; stops early on `.failed`.
-/
private def processH1Events
    {σ β : Type} [Handler σ] [Body β]
    (handler : σ) (config : Config) (connectionContext : CancellationContext)
    (events : Array (H1.Event .receiving))
    (state : ConnectionState β)
    : Async (ConnectionState β) := do

  let mut st := state

  for event in events do
    match event with
    | .needMoreData expect =>
      st := { st with requiresData := true, expectData := expect }

    | .needAnswer => pure ()

    | .endHeaders head =>

      -- Sets the pending head and removes the KeepAlive or Header timeout.
      st := { st with
        currentTimeout := config.lingeringTimeout
        keepAliveTimeout := none
        headerTimeout := none
        pendingHead := some head
      }

      if let some length := head.getSize true then
        -- Sets the size of the body that is going out of the connection.
        Body.setKnownSize st.requestStream (some length)

    | .«continue» =>
      if let some head := st.pendingHead then
        let (newMachine, clearPending) ← handleContinueEvent handler st.machine head config connectionContext
        st := { st with machine := newMachine }
        if clearPending then
          st := { st with pendingHead := none }

    | .next =>
      -- Reset all per-request state for the next pipelined request.
      if ¬(← Body.isClosed st.requestStream) then
        Body.close st.requestStream

      if let some res := st.respStream then
        if ¬(← Body.isClosed res) then
          Body.close res

      let newStream ← Body.mkStream

      st := { st with
        requestStream := newStream
        response := ← Std.Channel.new
        respStream := none
        keepAliveTimeout := some config.keepAliveTimeout.val
        currentTimeout := config.keepAliveTimeout.val
        headerTimeout := none
        handlerDispatched := false
      }

    | .failed err =>
      Handler.onFailure handler (toString err)

      if ¬(← Body.isClosed st.requestStream) then
        Body.close st.requestStream

      st := { st with requiresData := false, pendingHead := none }
      break

    | .closeBody =>
      if ¬(← Body.isClosed st.requestStream) then
        Body.close st.requestStream

    | .close => pure ()

  return st

/--
Dispatches a pending request head to the handler if one is waiting.
Spawns the handler as an async task and routes its result back through `state.response`.
Returns the updated state with `pendingHead` cleared and `handlerDispatched` set.
-/
private def dispatchPendingRequest
    {σ : Type} [Handler σ]
    (handler : σ) (extensions : Extensions) (connectionContext : CancellationContext)
    (state : ConnectionState (Handler.ResponseBody σ))
    : Async (ConnectionState (Handler.ResponseBody σ)) := do
  if let some line := state.pendingHead then

    let task ← Handler.onRequest handler { line, body := state.requestStream, extensions } connectionContext
      |>.asTask

    BaseIO.chainTask task (discard ∘ state.response.send)
    return { state with pendingHead := none, handlerDispatched := true }
  else
    return state

/--
Attempts a single non-blocking receive from the body and feeds any available chunk
into the machine, without going through the `Selectable.one` scheduler.

For fully-buffered bodies (e.g. `Body.Full`) this avoids one
`Selectable.one` round-trip when the chunk is already in memory. Streaming bodies
that have no producer waiting return `none` and fall through to the normal poll loop
unchanged.

Only one chunk is consumed here. Looping would introduce yield points between
`Body.tryRecv` calls, allowing a background producer to race ahead and close the
stream before `writeHead` runs — turning a streaming response with unknown size
into a fixed-length one.
-/
private def tryDrainBody [Body β]
    (machine : H1.Machine .receiving) (body : β)
    : Async (H1.Machine .receiving × Option β) := do
  match ← Body.tryRecv body with
  | none => pure (machine, some body)
  | some (some chunk) => pure (machine.sendData #[chunk], some body)
  | some none =>
    if !(← Body.isClosed body) then Body.close body
    pure (machine.userClosedBody, none)

/--
Processes a single async I/O event and updates the connection state.
Returns the updated state and `true` if the connection should be closed immediately.
-/
private def handleRecvEvent
    {σ β : Type} [Handler σ] [Body β]
    (handler : σ) (config : Config)
    (event : Recv β) (state : ConnectionState β)
    : Async (ConnectionState β × Bool) := do

  match event with
  | .bytes (some bs) =>

    let mut st := state

    -- After the first byte after idle we switch from keep-alive timeout to per-request header timeout.
    if st.keepAliveTimeout.isSome then
      st := { st with
        keepAliveTimeout := none
        headerTimeout := some <| (← Timestamp.now) + config.headerTimeout
      }

    return ({ st with machine := st.machine.feed bs }, false)

  | .bytes none =>
    return ({ state with machine := state.machine.noMoreInput }, false)

  | .responseBody (some chunk) =>
    return ({ state with machine := state.machine.sendData #[chunk] }, false)

  | .responseBody none =>
    if let some res := state.respStream then
      if ¬(← Body.isClosed res) then Body.close res
    return ({ state with machine := state.machine.userClosedBody, respStream := none }, false)

  | .bodyInterest interested =>
    if interested then
      let (newMachine, pulledChunk) := state.machine.pullBody
      let mut st := { state with machine := newMachine }

      if let some pulled := pulledChunk then
        try st.requestStream.send pulled.chunk pulled.incomplete
        catch e => Handler.onFailure handler e
        if pulled.final then
          if ¬(← Body.isClosed st.requestStream) then
            Body.close st.requestStream

      return (st, false)
    else
      return (state, false)

  | .close | .keepAliveTimeout => return (state, true)

  | .timeout =>
    Handler.onFailure handler "request header timeout"
    return ({ state with machine := state.machine.closeWithError .requestTimeout, handlerDispatched := false }, false)

  | .shutdown =>
    return ({ state with machine := state.machine.closeWithError .serviceUnavailable, handlerDispatched := false }, false)

  | .response (.error err) =>
    Handler.onFailure handler err
    return ({ state with machine := state.machine.closeWithError .internalServerError, handlerDispatched := false }, false)

  | .response (.ok res) =>
    if state.machine.failed then
      if ¬(← Body.isClosed res.body) then Body.close res.body
      return ({ state with handlerDispatched := false }, false)
    else
      let state ← refreshDate config state
      let (newMachine, newRespStream) ← applyResponse state.machine res

      -- Eagerly consume one chunk if immediately available (avoids a Selectable.one round-trip).
      let (drainedMachine, drainedRespStream, shouldClose) ←
        match newRespStream with
        | none => pure (newMachine, none, false)
        | some body =>
          try
            let (machine, body) ← tryDrainBody newMachine body
            pure (machine, body, false)
          catch e =>
            Handler.onFailure handler e
            pure (newMachine, some body, true)

      return ({ state with machine := drainedMachine, handlerDispatched := false, respStream := drainedRespStream }, shouldClose)

/--
Computes the active `PollSources` for the current connection state.
Determines which IO sources need attention and whether to include the socket.
-/
private def buildPollSources
    {α β : Type} [Transport α]
    (socket : α) (connectionContext : CancellationContext) (state : ConnectionState β)
    : Async (PollSources α β) := do
  let requestBodyOpen ←
    if state.machine.canPullBody then pure !(← Body.isClosed state.requestStream)
    else pure false

  let requestBodyInterested ←
    if state.machine.canPullBody ∧ requestBodyOpen then state.requestStream.hasInterest
    else pure false

  let requestBody ←
    if state.machine.canPullBodyNow ∧ requestBodyOpen then pure (some state.requestStream)
    else pure none

  -- Include the socket only when there is more to do than waiting for the handler alone.
  let pollSocket :=
    state.requiresData ∨ !state.handlerDispatched ∨ state.respStream.isSome ∨
    state.machine.writer.sentMessage ∨ (state.machine.canPullBody ∧ requestBodyInterested)

  return {
    socket := if pollSocket then some socket else none
    expect := state.expectData
    response := if state.handlerDispatched then some state.response else none
    responseBody := state.respStream
    requestBody := requestBody
    timeout := state.currentTimeout
    keepAliveTimeout := state.keepAliveTimeout
    headerTimeout := state.headerTimeout
    connectionContext := connectionContext
  }

/--
Whether processing `event` may run handler code that must not run after an earlier write failed:
the handler of a request with an unsafe method, or `Handler.onContinue`. Pipelined requests with
safe methods may be processed before the earlier responses are written (RFC 9112 §9.3.2).
-/
private def needsWrittenOutput : H1.Event .receiving → Bool
  | .endHeaders head => !head.method.isSafe
  | .«continue» => true
  | _ => false

/--
Reports a failed write of `outbox` to the handler, once.
-/
private def reportWriteFailure [Handler σ] (handler : σ) (outbox : Outbox α) : Async Unit := do
  if let some err ← outbox.takeError? then
    Handler.onFailure handler err

/--
Runs the main request/response processing loop for a single connection.
Drives the HTTP/1.1 state machine through four phases each iteration:
hand output to the outbox, process H1 events, dispatch pending requests, poll for I/O.
-/
private def handle
    {σ : Type} [Transport α] [h : Handler σ]
    (connection : Connection α)
    (config : Config)
    (connectionContext : CancellationContext)
    (handler : σ) : Async Unit := do

  let _ : Body (Handler.ResponseBody σ) := Handler.responseBodyInstance

  let socket := connection.socket
  let initStream ← Body.mkStream

  let mut state : ConnectionState (Handler.ResponseBody σ) := {
    machine := connection.machine
    requestStream := initStream
    keepAliveTimeout := some config.keepAliveTimeout.val
    currentTimeout := config.keepAliveTimeout.val
    headerTimeout := none
    response := ← Std.Channel.new
    respStream := none
    requiresData := false
    expectData := none
    handlerDispatched := false
    pendingHead := none
  }

  let outbox ← Outbox.new socket

  while ¬state.machine.halted do

    -- Phase 1: advance the state machine and hand its output to the outbox.
    state ← refreshDate config state
    let (newMachine, step) := state.machine.step
    state := { state with machine := newMachine }

    unless ← outbox.push step.output do
      reportWriteFailure handler outbox
      break

    if step.events.any needsWrittenOutput then
      unless ← outbox.awaitWritten do
        reportWriteFailure handler outbox
        break

    -- Phase 2: process all events emitted by this step.
    state ← processH1Events handler config connectionContext step.events state

    -- Phase 3: dispatch any newly parsed request to the handler.
    state ← dispatchPendingRequest handler connection.extensions connectionContext state

    -- Phase 4: wait for the next IO event when any source needs attention.
    if state.requiresData ∨ state.handlerDispatched ∨ state.respStream.isSome ∨ state.machine.canPullBody then
      state := { state with requiresData := false }
      let sources ← buildPollSources socket connectionContext state
      let event ← pollNextEvent config handler sources
      -- The connection is not idle while the peer still reads the response, so the keep-alive
      -- timeout starts over once the response is written.
      if event matches .keepAliveTimeout then
        if ← outbox.writing then
          outbox.awaitIdle
          continue
      let (newState, shouldClose) ← handleRecvEvent handler config event state
      state := newState
      if shouldClose then break

  -- Clean up: close all open streams, finish writing, and close the socket.
  if ¬(← Body.isClosed state.requestStream) then
    Body.close state.requestStream

  if let some res := state.respStream then
    if ¬(← Body.isClosed res) then Body.close res

  outbox.awaitIdle
  reportWriteFailure handler outbox
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
