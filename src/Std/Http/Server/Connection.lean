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
public import Std.Http.Protocol.H1
public import Std.Http.Server.Config
public import Std.Http.Server.Handler
import Std.Async.Watchdog

public section

namespace Std
namespace Http
namespace Server

open Std Async TCP Protocol
open Time

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
Events the connection loop reacts to: data from the peer, the response and its body, the request
body's reader, and the connection ending.
-/
private inductive Recv (β : Type)
  | bytes (x : Option ByteArray)
  | responseBody (x : Option Chunk)
  | bodyInterest (x : Bool)
  | response (x : (Except IO.Error (Response β)))
  | timeout
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
  connectionContext : CancellationContext
  idle : Bool

/--
Only the socket is awaited, so the connection can receive from it directly instead of selecting.
-/
private def PollSources.socketOnly (sources : PollSources α β) : Bool :=
  sources.socket.isSome && sources.response.isNone && sources.responseBody.isNone &&
    sources.requestBody.isNone

/--
How many bytes to ask the transport for in one receive.
-/
private def recvSize (config : Config) (expect : Option Nat) : UInt64 :=
  expect.getD config.defaultPayloadBytes |>.min config.maximumRecvSize |>.toUInt64

/--
The event to report once the connection context is cancelled. The connection's own timeout closes
an idle connection without a response and answers a started request with 408.
-/
private def cancelledEvent (wd : Watchdog) (ctx : CancellationContext) (idle : Bool) :
    BaseIO (Recv β) := do
  if ← wd.hasFired then
    return if idle then .close else .timeout
  match ← ctx.getCancellationReason with
  | some .deadline => return .timeout
  | _ => return .shutdown

/--
Waits for the next I/O event across all active sources described by `sources`.
Computes the socket recv size from `config`, then races all active selectables.
Calls `Handler.onFailure` and returns `.close` on transport errors.
-/
private def pollNextEvent
    {σ β : Type} [Transport α] [Handler σ] [Body β]
    (config : Config) (handler : σ) (wd : Watchdog) (sources : PollSources α β)
    : Async (Recv β) := do
  let ctx := sources.connectionContext
  let mut selectables : Array (Selectable (Recv β)) := #[
    .case ctx.doneSelector (fun _ => cancelledEvent wd ctx sources.idle)
  ]

  if let some socket := sources.socket then
    let size := recvSize config sources.expect
    selectables := selectables.push (.case (Transport.recvSelector socket size) (Recv.bytes · |> pure))

  if let some responseBody := sources.responseBody then
    selectables := selectables.push (.case (Body.recvSelector responseBody) (Recv.responseBody · |> pure))

  if let some requestBody := sources.requestBody then
    selectables := selectables.push (.case (requestBody.interestSelector) (Recv.bodyInterest · |> pure))

  if let some response := sources.response then
    selectables := selectables.push (.case response.recvSelector fun result => do
      unless ← ctx.isCancelled do
        return .response result
      if let .ok res := result then
        if ¬(← Body.isClosed res.body) then Body.close res.body
      cancelledEvent wd ctx sources.idle)

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
Injects a `Date` header into a response head if `Config.generateDate` is set
and the response does not already include one. `cache` holds the last value with its second, so
the date is formatted at most once per second.
-/
private def prepareResponseHead (config : Config) (cache : Option (Int × Header.Value)) (head : Response.Head) : Async (Response.Head × Option (Int × Header.Value)) := do
  if config.generateDate ∧ ¬head.headers.contains Header.Name.date then
    let now ← Timestamp.now
    let second := now.toSecondsSinceUnixEpoch.val
    let value :=
      match cache with
      | some (cached, value) =>
        if cached == second then value
        else Header.Value.ofString! (DateTime.ofTimestamp now TimeZone.ZoneRules.UTC).toHTTPDateString
      | none => Header.Value.ofString! (DateTime.ofTimestamp now TimeZone.ZoneRules.UTC).toHTTPDateString
    return ({ head with headers := head.headers.insert Header.Name.date value }, some (second, value))
  else
    return (head, cache)

/--
Applies a successful handler response to the machine.
Optionally injects a `Date` header, records the known body size, and sends the
response head. Returns the updated machine and the body stream to drain, or `none`
when the body should be omitted (e.g., for HEAD requests).
-/
private def applyResponse
    {β : Type} [Body β]
    (config : Config) (dateCache : Option (Int × Header.Value)) (machine : H1.Machine .receiving)
    (res : Response β) : Async (H1.Machine .receiving × Option β × Option (Int × Header.Value)) := do
  let size ← Body.getKnownSize res.body

  let machineSized :=
    if let some knownSize := size
      then machine.setKnownSize knownSize
      else machine

  let (responseHead, dateCache) ← prepareResponseHead config dateCache res.line
  let machineWithHead := machineSized.send responseHead
  if machineWithHead.omitsBody then
    if ¬(← Body.isClosed res.body) then
      Body.close res.body
    return (machineWithHead, none, dateCache)
  else
    return (machineWithHead, some res.body, dateCache)

/--
All mutable state carried through the connection processing loop.
Bundled into a struct so it can be passed to and returned from helper functions.
-/
private structure ConnectionState (β : Type) where
  machine : H1.Machine .receiving
  requestStream : Body.Stream
  /-- When the head of the request being received must be complete, once it started arriving. -/
  headerDeadline : Option Nat := none
  response : Option (Std.Channel (Except IO.Error (Response β))) := none
  respStream : Option β := none
  dateCache : Option (Int × Header.Value) := none
  handlerDispatched : Bool := false
  pendingHead : Option Request.Head := none

namespace ConnectionState

/--
The connection can only make progress after an event: data from the peer, the handler's response,
a chunk of the response body, or the request body's reader asking for more.
-/
private def needsEvent (state : ConnectionState β) : Bool :=
  state.machine.needsInput.isSome || state.handlerDispatched || state.respStream.isSome ||
    state.machine.canPullBody

end ConnectionState

/--
Processes all H1 events from a single machine step, updating the connection state.
Handles per-request resets, body-size tracking, `Expect: 100-continue`, and parse errors.
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
    | .endHeaders head =>
      st := { st with pendingHead := some head }

      if let some length := head.getSize true then
        -- Sets the size of the body that is going out of the connection.
        Body.setKnownSize st.requestStream (some length)
        -- An empty body is complete already, so the handler reads EOF without the connection
        -- having to pump it.
        if length == .fixed 0 then
          Body.close st.requestStream

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
        response := none
        respStream := none
        handlerDispatched := false
      }

    | .failed err =>
      Handler.onFailure handler (toString err)

      if ¬(← Body.isClosed st.requestStream) then
        Body.close st.requestStream

      st := { st with pendingHead := none }
      break

    | .closeBody =>
      if ¬(← Body.isClosed st.requestStream) then
        Body.close st.requestStream

    | .needMoreData _ | .needAnswer | .close => pure ()

  return st

/--
At most this many request body bytes are pushed to the request stream before its handler runs.
-/
private def prefillLimit : Nat := 65536

/--
Pushes the request body bytes the machine already holds to the request stream, so that a handler
reading a body that arrived with its head does not have to suspend. The rest of the body is pulled
on demand, and a request over a limit fails only once its handler reads that far. Also returns
whether the whole body is in the stream.
-/
private def prefillRequestBody [Handler σ] (handler : σ) (state : ConnectionState β) :
    Async (ConnectionState β × Bool) := do
  if ← state.requestStream.isClosedForSend then
    return (state, true)

  let (machine, chunks) := state.machine.pullBuffered prefillLimit
  -- An `Async` `for` over an array stays on this thread, unlike a `while` loop.
  for pulled in chunks do
    try state.requestStream.push pulled.chunk pulled.incomplete
    catch e => Handler.onFailure handler e
  let complete := chunks.back?.any (·.final)
  if complete then
    Body.close state.requestStream
  return ({ state with machine }, complete)

/--
How the connection loop runs handlers, shared with the cancellation watcher of `handle`.

A handler runs inline on the loop's thread until it first suspends, so one that blocks keeps the
loop from seeing a cancellation. The watcher then finishes the connection in its place.
-/
private inductive Dispatch
  | spawn
  | inline
  | running
  | cancelled

/--
Runs the handler for the request head `line`.
The handler runs inline until it first suspends, if `mayInline` and unless `dispatch` says
otherwise. A handler that finishes without suspending returns its result directly; otherwise its
result is routed back through `state.response`. Returns `none` when the cancellation watcher
finished the connection while the handler ran.
-/
private def startHandler
    {σ : Type} [Handler σ]
    (handler : σ) (extensions : Extensions) (connectionContext : CancellationContext)
    (dispatch : IO.Ref Dispatch) (mayInline : Bool) (line : Request.Head)
    (state : ConnectionState (Handler.ResponseBody σ))
    : Async (Option (ConnectionState (Handler.ResponseBody σ) ×
        Option (Except IO.Error (Response (Handler.ResponseBody σ))))) := do
  let _ : Body (Handler.ResponseBody σ) := Handler.responseBodyInstance

  let action := Handler.onRequest handler { line, body := state.requestStream, extensions } connectionContext

  -- One `BaseIO` action, since every `Async` bind here allocates its continuation up front.
  let started? : Option (MaybeTask (Except IO.Error (Response (Handler.ResponseBody σ)))) ←
    liftM (m := BaseIO) do
      let inline ←
        if mayInline then
          dispatch.modifyGet fun
            | .inline => (true, .running)
            | d => (false, d)
        else
          pure false

      unless inline do
        return some (MaybeTask.ofTask (← BaseAsync.asTask action))

      let started ← BaseAsync.toRawBaseIO action
      let kept ← dispatch.modifyGet fun
        | .running => (true, .inline)
        | d => (false, d)

      if kept then
        return some started

      -- Nobody reads the response any more, so release its body here.
      BaseIO.chainTask started.toTask fun
        | .ok res => discard <| EAsync.toBaseIO (ε := IO.Error) do
          if ¬(← Body.isClosed res.body) then Body.close res.body
        | .error _ => pure ()
      return none

  let some started := started?
    | return none

  match started with
  | MaybeTask.pure result =>
    return some (state, some result)
  | MaybeTask.ofTask task =>
    let response ← Std.Channel.new
    BaseIO.chainTask task (discard ∘ response.send)
    return some ({ state with handlerDispatched := true, response := some response }, none)

/--
Dispatches a pending request head to the handler if one is waiting, after pushing the body bytes
already received to the request stream. See `startHandler`.
-/
private def dispatchPendingRequest
    {σ : Type} [Handler σ]
    (handler : σ) (extensions : Extensions) (connectionContext : CancellationContext)
    (dispatch : IO.Ref Dispatch)
    (state : ConnectionState (Handler.ResponseBody σ))
    : Async (Option (ConnectionState (Handler.ResponseBody σ) ×
        Option (Except IO.Error (Response (Handler.ResponseBody σ))))) := do
  let some line := state.pendingHead
    | return some (state, none)

  let state := { state with pendingHead := none }
  -- A request without a body skips the pre-fill, whose `Async` bind would allocate for it.
  if state.machine.hasEmptyBody then
    startHandler handler extensions connectionContext dispatch true line state
  else
    let (state, complete) ← prefillRequestBody handler state
    -- Only the loop delivers the rest of a body, so a handler that blocks its thread waiting for it
    -- must not run on the loop's thread.
    startHandler handler extensions connectionContext dispatch complete line state

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
into a fixed-length one. A fixed-size body cannot change its framing, so its end is
taken as well, which lets the head and the whole body go out in one write.
-/
private def tryDrainBody [Body β]
    (machine : H1.Machine .receiving) (body : β)
    : Async (H1.Machine .receiving × Option β) := do
  match ← Body.tryRecv body with
  | none => pure (machine, some body)
  | some (some chunk) =>
    let machine := machine.sendData #[chunk]
    if machine.hasFixedLengthOutput then
      match ← Body.tryRecv body with
      | some none =>
        if !(← Body.isClosed body) then Body.close body
        pure (machine.userClosedBody, none)
      | some (some chunk) => pure (machine.sendData #[chunk], some body)
      | none => pure (machine, some body)
    else
      pure (machine, some body)
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
    return ({ state with machine := state.machine.feed bs }, false)

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

  | .close => return (state, true)

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
      let (newMachine, newRespStream, dateCache) ← applyResponse config state.dateCache state.machine res
      let state := { state with dateCache }

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
  -- A stream its reader closed is done even while pushed chunks are left unread in it.
  let requestBodyOpen ←
    if state.machine.canPullBody then pure !(← state.requestStream.isClosedForSend)
    else pure false

  let requestBodyInterested ←
    if state.machine.canPullBody ∧ requestBodyOpen then state.requestStream.hasInterest
    else pure false

  let requestBody ←
    if state.machine.canPullBodyNow ∧ requestBodyOpen then pure (some state.requestStream)
    else pure none

  -- Include the socket only when there is more to do than waiting for the handler alone.
  let pollSocket :=
    state.machine.needsInput.isSome ∨ !state.handlerDispatched ∨ state.respStream.isSome ∨
    state.machine.isSendingMessage ∨ (state.machine.canPullBody ∧ requestBodyInterested)

  return {
    socket := if pollSocket then some socket else none
    expect := state.machine.needsInput.join
    response := if state.handlerDispatched then state.response else none
    responseBody := state.respStream
    requestBody := requestBody
    connectionContext := connectionContext
    idle := state.machine.isReaderIdle
  }

/--
The header deadline for the next wait: a request head that started arriving has to be complete
within the header timeout.
-/
private def nextHeaderDeadline (config : Config) (state : ConnectionState β) :
    BaseIO (Option Nat) := do
  if state.machine.isReaderIdle || !state.machine.isReaderReadingHead then
    return none
  if let some deadline := state.headerDeadline then
    return some deadline
  return some ((← IO.monoMsNow) + config.headerTimeout.toInt.toNat)

/--
What the connection waited for last, handled at the start of the next loop iteration.
-/
private inductive Input (β : Type) where
  | none
  | event (event : Recv β)
  | received (result : Except IO.Error (Option ByteArray))

/--
Turns what the last wait produced into the event to handle, if any.
-/
private def inputEvent? [Handler σ] (handler : σ) (wd : Watchdog) (ctx : CancellationContext)
    (idle : Bool) (input : Input β) : Async (Option (Recv β)) := do
  match input with
  | .none => return none
  | .event event => return some event
  | .received result =>
    -- An interrupted receive fails, so a timeout or a cancellation takes precedence over its result.
    if (← wd.disarm) || (← ctx.isCancelled) then
      return some (← cancelledEvent wd ctx idle)

    match result with
    | .ok bytes => return some (.bytes bytes)
    | .error err =>
      Handler.onFailure handler err
      return some .close

/--
Continues with `k` applied to the result of `task` on the thread that completes it, so that no task
of its own is scheduled.
-/
@[inline]
private def continueWith (task : ETask IO.Error α) (k : Except IO.Error α → β) : Async β :=
  BaseAsync.ofTask (Task.map (sync := true) (fun result => (Except.ok (k result) : Except IO.Error β)) task)

/--
The state of an `Outbox`.
-/
private structure OutboxState where
  /-- Output handed over while a write was in flight, written together once it completes. -/
  queued : Array ByteArray := #[]
  queuedBytes : Nat := 0
  writing : Bool := false
  /-- A write failed, so later output is dropped. -/
  failed : Bool := false
  /-- The failure, until it is reported to the handler. -/
  error : Option IO.Error := none
  /-- Resolved once no write is in flight. -/
  idle : Option (IO.Promise Unit) := none

/--
Writes a connection's output in order without the connection waiting for it: output handed over
while a write is in flight goes out in a single write once that write completes. The responses to
earlier requests thus keep going out while a handler blocks the connection's thread, and the
cancellation watcher can answer after them.
-/
private abbrev Outbox := IO.Ref OutboxState

namespace Outbox

/--
Starts writing `data`, then whatever was queued meanwhile once the write completes. The next write
starts on the thread that completed the previous one, which for a socket is the event loop's own, so
it does not have to wait for the event loop.
-/
private partial def write [Transport α] (outbox : Outbox) (socket : α) (data : Array ByteArray) :
    BaseIO Unit := do
  let task ← EAsync.toBaseIO (Transport.sendAll socket data)
  BaseIO.chainTask (sync := true) task fun result => do
    let (next, idle) ← outbox.modifyGet fun s =>
      match result with
      | .error err =>
        ((#[], s.idle), { s with
          queued := #[], queuedBytes := 0, writing := false, failed := true, error := some err
          idle := none })
      | .ok () =>
        if s.queued.isEmpty then ((#[], s.idle), { s with writing := false, idle := none })
        else ((s.queued, none), { s with queued := #[], queuedBytes := 0 })
    if let some idle := idle then
      idle.resolve ()
    unless next.isEmpty do
      outbox.write socket next

/--
The outbox queues up to this many bytes before the connection waits for its writes.
-/
private def limit : Nat := 65536

/--
Hands `data`, `size` bytes, to the outbox, which writes it after everything handed over before.
Returns how many bytes now wait behind the write in flight, or `none` if a write failed and `data`
was dropped.
-/
private def send [Transport α] (outbox : Outbox) (socket : α) (data : Array ByteArray) (size : Nat) :
    BaseIO (Option Nat) := do
  let (start, queued?) ← outbox.modifyGet fun s =>
    if s.failed then ((false, none), s)
    else if s.writing then
      let queuedBytes := s.queuedBytes + size
      ((false, some queuedBytes), { s with queued := s.queued ++ data, queuedBytes })
    else ((true, some 0), { s with writing := true })
  if start then
    outbox.write socket data
  return queued?

/--
A task that finishes once no write is in flight, or `none` if none is.
-/
private def idle? (outbox : Outbox) : BaseIO (Option (Task (Option Unit))) := do
  unless (← outbox.get).writing do
    return none
  let fresh ← IO.Promise.new
  outbox.modifyGet fun s =>
    if !s.writing then (none, s)
    else match s.idle with
      | some idle => (some idle.result?, s)
      | none => (some fresh.result?, { s with idle := some fresh })

/--
Waits until no write is in flight.
-/
private def awaitIdle (outbox : Outbox) : Async Unit := do
  if let some idle ← outbox.idle? then
    BaseAsync.ofTask (Task.map (sync := true) (fun _ => (Except.ok () : Except IO.Error Unit)) idle)

/--
Reports a failed write to the handler, once. Returns `false` if a write failed.
-/
private def check [Handler σ] (handler : σ) (outbox : Outbox) : Async Bool := do
  unless (← outbox.get).failed do
    return true
  if let some err ← outbox.modifyGet fun s => (s.error, { s with error := none }) then
    Handler.onFailure handler err
  return false

/--
Hands `buffer` to the outbox, then waits for its writes if more than `limit` bytes are queued, so a
peer that does not read holds up the connection instead of growing its memory. Returns `false` after
reporting a failed write to the handler.
-/
private def push [Transport α] [Handler σ] (handler : σ) (socket : α) (outbox : Outbox)
    (buffer : Internal.ChunkedBuffer) : Async Bool := do
  if buffer.size = 0 then
    return true
  match ← outbox.send socket buffer.data buffer.size with
  | some queued =>
    if queued < limit then
      return true
    outbox.awaitIdle
    outbox.check handler
  | none => outbox.check handler

/--
Waits until every write has completed, reporting a failed one to the handler.
-/
private def finish [Handler σ] (handler : σ) (outbox : Outbox) : Async Unit := do
  outbox.awaitIdle
  discard <| outbox.check handler

end Outbox

/--
Times a wait on the socket with the watchdog: the keep-alive timeout while the connection is idle,
starting once its writes complete since the peer may still be reading the response; the header
timeout while a request head arrives; and the lingering timeout otherwise.
-/
private def armSocketWait (config : Config) (wd : Watchdog) (outbox : Outbox)
    (state : ConnectionState β) : BaseIO Unit := do
  if state.machine.isReaderIdle then
    if let some idle ← outbox.idle? then
      wd.armAfter idle config.keepAliveTimeout.val
    else
      wd.arm config.keepAliveTimeout.val
  else if let some deadline := state.headerDeadline then
    wd.armUntil deadline
  else
    wd.arm config.lingeringTimeout

private structure Loop (β : Type) where
  state : ConnectionState β
  input : Input β := .none
  abandoned : Bool := false

/--
Waits for the next event across every active source and continues with `k`. A deadline that
passed while another source won is reported instead of that source's event.
-/
private def selectNext [Transport α] [Handler σ] [Body β] (config : Config) (handler : σ)
    (wd : Watchdog) (sources : PollSources α β) (k : Input β → γ) : Async γ := do
  let event ← pollNextEvent config handler wd sources
  if ← wd.disarm then
    return k (.event (← cancelledEvent wd sources.connectionContext sources.idle))
  return k (.event event)

/--
Starts waiting for the connection's next event and continues with `k`. Waits on the socket are
timed by the watchdog. When only the socket is awaited and the transport can interrupt a receive,
the connection receives directly and `k` runs on the thread that completes the receive, so the
wait costs no task of its own; otherwise it selects over every active source.
-/
private def wait [Transport α] [Handler σ] [Body β] (socket : α) (config : Config) (handler : σ)
    (connectionContext : CancellationContext) (wd : Watchdog) (interrupt? : Option (α → IO Unit))
    (outbox : Outbox) (state : ConnectionState β) (k : Input β → γ) : Async γ := do
  let sources ← buildPollSources socket connectionContext state
  if sources.socket.isNone then
    selectNext config handler wd sources k
  else
    armSocketWait config wd outbox state
    match interrupt? with
    | some interrupt =>
      if sources.socketOnly then
        let recv ← EAsync.toBaseIO (Transport.recv socket (recvSize config sources.expect))
        -- A cancellation that ran before the receive started could not interrupt it.
        if ← connectionContext.isCancelled then
          try interrupt socket catch _ => pure ()
        continueWith recv fun result => k (.received result)
      else
        selectNext config handler wd sources k
    | none => selectNext config handler wd sources k

/--
One iteration of the connection loop: handles what the last wait produced, advances the state
machine and hands its output to the outbox, runs the handler for a new request, then starts the
next wait.
-/
private def iterate
    {σ : Type} [Transport α] [Handler σ] [Body (Handler.ResponseBody σ)]
    (socket : α) (config : Config) (handler : σ) (extensions : Extensions)
    (connectionContext : CancellationContext) (wd : Watchdog) (interrupt? : Option (α → IO Unit))
    (dispatch : IO.Ref Dispatch) (outbox : Outbox)
    (loop : Loop (Handler.ResponseBody σ)) : Async (ForInStep (Loop (Handler.ResponseBody σ))) := do
  let mut state := loop.state

  if let some event ← inputEvent? handler wd connectionContext state.machine.isReaderIdle loop.input then
    let (newState, shouldClose) ← handleRecvEvent handler config event state
    state := newState
    if shouldClose then
      return .done { state }

  if state.machine.halted then
    return .done { state }

  let (machine, step) := state.machine.step
  state := { state with machine }
  -- Handed over at once, so that a handler blocking its thread does not hold up earlier responses.
  unless ← outbox.push handler socket step.output do
    return .done { state }

  state ← processH1Events handler config connectionContext step.events state

  -- A handler that finishes without suspending is answered within this iteration.
  let some (newState, result?) ← dispatchPendingRequest handler extensions connectionContext dispatch
      state
    | return .done { state, abandoned := true }

  state := newState

  if let some result := result? then
    let (newState, shouldClose) ← handleRecvEvent handler config (.response result) state
    let loop : Loop _ := { state := newState }
    return if shouldClose then .done loop else .yield loop

  unless state.needsEvent do
    return .yield { state }

  state := { state with headerDeadline := ← nextHeaderDeadline config state }

  wait socket config handler connectionContext wd interrupt? outbox state fun input =>
    .yield { state, input }

/--
Runs the request/response processing loop for a single connection until it ends, then writes the
remaining output and closes the streams and the socket. Returns `false`, without cleaning up, when
the cancellation watcher finished the connection while a handler ran inline.
-/
private def run
    {σ : Type} [Transport α] [h : Handler σ]
    (connection : Connection α) (config : Config) (handler : σ)
    (connectionContext : CancellationContext) (wd : Watchdog) (interrupt? : Option (α → IO Unit))
    (dispatch : IO.Ref Dispatch) (outbox : Outbox) : Async Bool := do

  let _ : Body (Handler.ResponseBody σ) := Handler.responseBodyInstance

  let socket := connection.socket

  let init : Loop (Handler.ResponseBody σ) := {
    state := { machine := connection.machine, requestStream := ← Body.mkStream }
  }

  let final ←
    try
      EAsync.forIn init fun _ loop =>
        iterate socket config handler connection.extensions connectionContext wd interrupt? dispatch
          outbox loop
    finally
      connectionContext.cancel .cancel

  if final.abandoned then
    if ¬(← Body.isClosed final.state.requestStream) then
      Body.close final.state.requestStream
    return false

  outbox.finish handler

  -- Close all open streams and the socket.
  let state := final.state
  if ¬(← Body.isClosed state.requestStream) then
    Body.close state.requestStream

  if let some res := state.respStream then
    if ¬(← Body.isClosed res) then Body.close res

  Transport.close socket
  return true

/--
Finishes a connection whose loop is held up by a handler running inline: answers the request as
the loop would have, after the output the loop handed to `outbox`, then closes the socket. The loop
closes the request body once the handler returns.
-/
private def abandon
    {σ : Type} [Transport α] [Handler σ]
    (connection : Connection α) (handler : σ) (wd : Watchdog) (ctx : CancellationContext)
    (outbox : Outbox) : Async Unit := do
  let status ←
    match ← cancelledEvent (β := Unit) wd ctx false with
    | .timeout =>
      Handler.onFailure handler "request header timeout"
      pure Status.requestTimeout
    | _ => pure Status.serviceUnavailable

  let response := H1.Machine.errorResponse connection.machine.config status
  discard <| outbox.send connection.socket response.data response.size
  outbox.finish handler

  Transport.close connection.socket

/--
Serves a single connection and waits until it is done. The loop resolves a promise when it ends
instead of returning through this call, so that a handler blocking the loop's thread cannot hold up
a cancellation: the watcher registered here then finishes the connection from another thread.
-/
private def handle
    {σ : Type} [Transport α] [h : Handler σ]
    (connection : Connection α)
    (config : Config)
    (parentContext : CancellationContext)
    (handler : σ) : Async Unit := do

  let _ : Body (Handler.ResponseBody σ) := Handler.responseBodyInstance

  let socket := connection.socket
  -- A child context, so that a timeout cancels only this connection.
  let connectionContext ← parentContext.fork
  let wd ← Watchdog.new connectionContext
  let interrupt? := Transport.interruptRecv? (α := α)
  let dispatch ← IO.mkRef Dispatch.spawn
  let outbox : Outbox ← IO.mkRef {}
  let finished : IO.Promise (Except IO.Error Unit) ← IO.Promise.new

  BaseIO.chainTask (← connectionContext.done) fun _ => do
    if let some interrupt := interrupt? then
      discard <| (interrupt socket).toBaseIO

    let running ← dispatch.modifyGet fun
      | .running => (true, .cancelled)
      | _ => (false, .cancelled)

    if running then
      let task ← (abandon connection handler wd connectionContext outbox).toBaseIO
      BaseIO.chainTask (sync := true) task finished.resolve

  -- Until this returns, the loop runs on this call's own stack, so handlers have to be spawned.
  let task ← (run connection config handler connectionContext wd interrupt? dispatch outbox).toBaseIO
  BaseIO.chainTask (sync := true) task fun
    | .ok true => finished.resolve (.ok ())
    | .ok false => pure ()
    | .error e => finished.resolve (.error e)

  dispatch.modify fun
    | .spawn => .inline
    | d => d

  Async.ofPromise (pure finished)

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
