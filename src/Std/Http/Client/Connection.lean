/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Async.TCP
public import Std.Async.ContextAsync
public import Std.Http.Transport
public import Std.Http.Protocol.H1
public import Std.Http.Client.Config

public section

/-!
# Connection

This module defines `Connection`, an HTTP/1.1 client connection that owns a single persistent
transport and dispatches sequential request/response exchanges over it. A background task drives
the processing loop; callers interact through a channel and receive their results on promises.

`Connection` is transport-agnostic at the type level: the transport type is consumed at construction
time (`Connection.new`) but is not stored in the struct, so `Connection` values are uniform
regardless of the underlying socket type.
-/

namespace Std.Http.Client

open Std Async TCP Protocol
open Time

set_option linter.all true

/--
A request queued to the background connection loop, paired with the promises that deliver its
outcome.
-/
structure PendingRequest where
  /--
  The request to send.
  -/
  request : Request Body.Any

  /--
  Promise resolved with the eventual response.
  -/
  responsePromise : IO.Promise (Except Error (Response Body.Stream))

  /--
  Promise resolved when the connection finishes this exchange and is ready for the next request,
  or when the exchange fails after the response headers were delivered.
  -/
  completionPromise : IO.Promise (Except Error Unit)

  /--
  Per-request overrides applied on top of the client `Config` for this exchange.
  -/
  requestOverrides : RequestOverrides := {}

namespace PendingRequest

/--
Resolves the request with an error.
-/
def onError (pending : PendingRequest) (error : Error) : BaseIO Unit := do
  pending.responsePromise.resolve (.error error)
  pending.completionPromise.resolve (.error error)

/--
Resolves the request with a response.
-/
def onResponse (pending : PendingRequest) (response : Response Body.Stream) : BaseIO Unit :=
  pending.responsePromise.resolve (.ok response)

/--
Resolves the request as completed successfully.
-/
def onComplete (pending : PendingRequest) : BaseIO Unit :=
  pending.completionPromise.resolve (.ok ())

end PendingRequest

/--
An HTTP client connection that sends sequential requests over a persistent transport.
-/
structure Connection where
  /--
  Queue of requests sent by callers.
  -/
  requestChannel : Std.CloseableChannel PendingRequest

  /--
  Resolves when the background loop exits.
  -/
  shutdown : IO.Promise Unit

  /--
  Configuration for this connection.
  -/
  config : Config

  /--
  Cancellation context driving the background loop. Canceling it aborts any in-flight exchange (the
  loop treats cancellation as a shutdown), which is how `close` interrupts a request that is blocked
  waiting on the socket rather than parked on the request channel.
  -/
  context : CancellationContext

  /--
  Unique identifier assigned by the pool when this connection is registered.
  Zero for connections created outside a pool.
  -/
  id : UInt64 := 0

namespace Connection

/--
Events produced by the async select loop in `pollNextEvent`.
Each variant corresponds to one possible outcome of waiting for I/O.
-/
private inductive Recv
  | bytes (x : Option ByteArray)
  | requestBody (x : Option Chunk)
  | bodyInterest (x : Bool)
  | request (x : Option PendingRequest)
  | timeout
  | continueTimeout
  | shutdown
  | close

/--
State that belongs to a single in-flight request/response exchange.
Kept in one struct so a `.next` transition can reset every per-request field
at once (impossible to forget one) and so `closeAll` has a self-contained target.
-/
structure InFlightState where
  /--
  The queued request whose promise is pending (or just resolved).
  -/
  pending : PendingRequest

  /--
  Body the writer pump is currently consuming. `none` while waiting for
  `100 Continue` (the body is stashed in `pendingRequestBody` until the
  server permits it).
  -/
  requestBody : Option Body.Any

  /--
  Body parked while waiting for a `100 Continue`.
  -/
  pendingRequestBody : Option Body.Any

  /--
  The outgoing response-body stream handed to the caller.
  -/
  responseStream : Option Body.Stream

  /--
  `true` while the machine is waiting for `100 Continue`.
  -/
  waitingForContinue : Bool

  /--
  Absolute deadline after which the body is sent without having seen `100 Continue`.
  `none` unless the request carries `Expect: 100-continue` and is still waiting.
  -/
  continueDeadline : Option Timestamp := none

  /--
  Cumulative response-body bytes pulled from the machine. Used to enforce `maxResponseBodySize`.
  -/
  downloadBodyBytes : UInt64 := 0

  /--
  `true` once the whole response body has been handed to the caller. The exchange succeeded from
  the caller's point of view even if the connection cannot be reused afterwards.
  -/
  responseComplete : Bool := false

namespace InFlightState

/--
Builds the initial `InFlightState` for a request that has just been handed to the machine, given the
stream allocated for the response. `awaitsContinue` comes from the machine and decides whether the
body is sent right away or parked until the server answers the expectation.
-/
def ofPending (pending : PendingRequest) (responseStream : Body.Stream)
    (continueDeadline : Timestamp) (awaitsContinue : Bool) : InFlightState where
  pending := pending
  requestBody := if awaitsContinue then none else some pending.request.body
  pendingRequestBody := if awaitsContinue then some pending.request.body else none
  responseStream := some responseStream
  waitingForContinue := awaitsContinue
  continueDeadline := if awaitsContinue then some continueDeadline else none

/--
Releases a body parked behind `Expect: 100-continue` so the writer pump starts sending it.
-/
def releasePendingBody (s : InFlightState) : InFlightState :=
  { s with
    requestBody := s.pendingRequestBody
    pendingRequestBody := none
    waitingForContinue := false
    continueDeadline := none
  }

/--
Closes every open resource tied to this in-flight exchange: both request
body handles and the response stream. Each close is guarded by an `isClosed`
check so this is idempotent.
-/
def closeAll (s : InFlightState) : Async Unit := do
  if let some body := s.requestBody then
    if ¬(← body.isClosed) then body.close

  if let some body := s.pendingRequestBody then
    if ¬(← body.isClosed) then body.close

  if let some body := s.responseStream then
    if ¬(← body.isClosed) then body.close

end InFlightState

/--
All mutable state carried through the connection processing loop.

Connection-level fields (`machine`, timeouts, read-pump flags) live here
directly; per-exchange fields are wrapped in `inFlight : Option InFlightState`
so that every transition to or from idle is a single field update that cannot
accidentally leave a stale per-request value behind.
-/
structure ConnectionState where
  /--
  The HTTP/1.1 state machine driving reads, writes, and parser events for
  this socket.
  -/
  machine : H1.Machine .sending

  /--
  The configuration governing the current exchange: the connection's `Config` with the in-flight
  request's `RequestOverrides` applied, or that `Config` unchanged while idle. Every setting
  consulted while running an exchange is read from here, so a new `RequestOverrides` field takes
  effect everywhere without hunting down call sites. The connection-wide config is passed
  explicitly to the two places that need the un-overridden values: applying a new request's
  overrides, and resetting to idle on `.next`.
  -/
  config : Config

  /--
  The timeout currently armed for the next blocking wait.
  -/
  currentTimeout : Millisecond.Offset

  /--
  The idle keep-alive timeout to use between requests, or `none` while a
  request/response exchange is active.
  -/
  keepAliveTimeout : Option Millisecond.Offset

  /--
  Preferred socket recv size from the most recent `.needMoreData` event.
  -/
  expectData : Option Nat

  /--
  `true` when the last step emitted `.needMoreData`, i.e. the parser ran out of input and cannot
  advance until more bytes arrive. Cleared before each poll and re-derived by the next step.
  -/
  requiresData : Bool := false

  /--
  `none` when the connection is idle (waiting for the next request).
  -/
  inFlight : Option InFlightState

  /--
  Absolute wall-clock deadline for the in-flight request/response exchange, or `none` while idle.
  Enforces `config.requestTimeout` as a bound on the *whole* exchange (send + receive), unlike
  `currentTimeout`, which only bounds the idle gap between successive I/O events. Set when a request
  goes in-flight and cleared on completion.
  -/
  requestDeadline : Option Timestamp := none

namespace ConnectionState

/--
`true` when the connection is waiting for the next request.
-/
@[inline]
def waitingForRequest (s : ConnectionState) : Bool :=
  s.inFlight.isNone

/--
Applies `f` to the current in-flight state, if any.
-/
@[inline]
def mapInFlight (s : ConnectionState) (f : InFlightState → InFlightState) : ConnectionState :=
  { s with inFlight := s.inFlight.map f }

/--
The request currently bound to the in-flight exchange, if any.
-/
@[inline]
def currentRequest (s : ConnectionState) : Option PendingRequest :=
  s.inFlight.map (·.pending)

/--
The request body currently being pumped to the wire, if any.
-/
@[inline]
def requestBody (s : ConnectionState) : Option Body.Any :=
  s.inFlight.bind (·.requestBody)

/--
The request body parked behind `Expect: 100-continue`, if any.
-/
@[inline]
def pendingRequestBody (s : ConnectionState) : Option Body.Any :=
  s.inFlight.bind (·.pendingRequestBody)

/--
The response stream currently exposed to the caller, if any.
-/
@[inline]
def responseStream (s : ConnectionState) : Option Body.Stream :=
  s.inFlight.bind (·.responseStream)

/--
`true` when the in-flight request is still waiting for `100 Continue`
before its body may be sent.
-/
@[inline]
def waitingForContinue (s : ConnectionState) : Bool :=
  s.inFlight.map (·.waitingForContinue) |>.getD false

/--
The deadline at which a body parked behind `Expect: 100-continue` is sent regardless.
-/
@[inline]
def continueDeadline (s : ConnectionState) : Option Timestamp :=
  s.inFlight.bind (·.continueDeadline)

/--
`true` when the loop depends on an external event to advance, which is exactly the set of sources
`pollNextEvent` races: bytes from the socket, the next request from the channel, the next chunk of
the outgoing body, or the caller pulling response body bytes. Events left on the machine by the
previous step are work in hand, so they take priority over parking.

Anything else means the last step left buffered work behind and the loop steps again rather than
waiting for an event that may never come.
-/
@[inline]
def waitingOnIO (s : ConnectionState) : Bool :=
  !s.machine.hasPendingEvents &&
    (s.requiresData || s.waitingForRequest || s.requestBody.isSome || s.machine.canPullBody)

end ConnectionState

/--
Closes every open per-request resource held by `state`. Idempotent.
-/
private def closeAllRequestState (state : ConnectionState) : Async Unit :=
  match state.inFlight with
  | some f => f.closeAll
  | none => pure ()

/--
Waits for the next I/O event across all sources relevant to `state`, racing every active selectable.
Returns `.close` on transport errors.
-/
private def pollNextEvent
    [Transport α]
    (socket : α)
    (requestChannel : Std.CloseableChannel PendingRequest)
    (connectionContext : CancellationContext)
    (state : ConnectionState) : Async Recv := do
  let responseStreamClosed ← match state.responseStream with
    | some body => Body.isClosed body
    | none => pure true

  let responseBodySource :=
    if state.machine.canPullBodyNow then
      match state.responseStream with
      | some body => if responseStreamClosed then none else some body
      | none => none
    else none

  let pollSocket := state.machine.needsInput

  let expectedBytes := state.expectData
    |>.getD state.config.defaultRequestBufferSize
    |>.min state.config.maxRecvChunkSize
    |>.toUInt64

  let mut selectables : Array (Selectable Recv) := #[
    .case connectionContext.doneSelector (fun _ => pure .shutdown)
  ]

  if pollSocket then
    selectables := selectables.push
      (.case (Transport.recvSelector socket expectedBytes) (fun bytes => pure (Recv.bytes bytes)))

    let timeout := state.keepAliveTimeout.getD state.currentTimeout
    selectables := selectables.push (.case (← Selector.sleep timeout) (fun _ => pure .timeout))

    if let some deadline := state.requestDeadline then
      let remaining := (deadline - (← Timestamp.now)).toMilliseconds
      selectables := selectables.push
        (.case (← Selector.sleep remaining) (fun _ => pure .timeout))

  else if let some idleTimeout := state.keepAliveTimeout then
    selectables := selectables.push
      (.case (← Selector.sleep idleTimeout) (fun _ => pure .timeout))

  if let some requestBody := state.requestBody then
    selectables := selectables.push
      (.case requestBody.recvSelector (fun chunk => pure (Recv.requestBody chunk)))

  -- RFC 9110 §10.1.1: a server may ignore `Expect: 100-continue` entirely, so the wait for the
  -- interim response is bounded; on expiry the body is sent as if `100 Continue` had arrived.
  if state.waitingForContinue then
    if let some deadline := state.continueDeadline then
      selectables := selectables.push
        (.case (← Selector.sleep (deadline - (← Timestamp.now)).toMilliseconds)
          (fun _ => pure .continueTimeout))

  if state.waitingForRequest then
    selectables := selectables.push
      (.case requestChannel.recvSelector (fun request => pure (Recv.request request)))

  if let some responseBody := responseBodySource then
    selectables := selectables.push
      (.case responseBody.interestSelector (fun interested => pure (Recv.bodyInterest interested)))

    if !pollSocket then
      selectables := selectables.push
        (.case (← Selector.sleep state.currentTimeout) (fun _ => pure .timeout))

  try Selectable.one selectables catch _ => pure .close

/--
Processes all H1 events from a single machine step, executing side effects
inline and returning the updated state together with a `sawFailure` flag
that tells the main loop to exit. Handles keep-alive resets, body-size
tracking, `Expect: 100-continue`, and parse errors.
-/
private def processH1Events
    (baseConfig : Config)
    (requestChannel : Std.CloseableChannel PendingRequest)
    (events : Array (H1.Event .sending))
    (state : ConnectionState) : Async (ConnectionState × Bool) := do
  let mut st := state
  let mut sawFailure := false

  for event in events do
    match event with
    | .needMoreData expect =>
      st := { st with requiresData := true, expectData := expect }

    | .needAnswer =>
      pure ()

    | .endHeaders head =>
      if head.status.isInformational then
        -- A `100 Continue` response authorizes the body: move it from the
        -- pending slot into `requestBody` so the pump loop starts sending.
        if head.status == .continue && st.waitingForContinue then
          st := st.mapInFlight (·.releasePendingBody)
      else
        st := { st with
          currentTimeout := st.config.readTimeout
          keepAliveTimeout := none
        }

        -- A non-informational response while we were still waiting for
        -- `100 Continue`: the server rejected (or bypassed) the expectation.
        -- Discard the pending body — it must not be sent.
        if st.waitingForContinue then
          if let some body := st.pendingRequestBody then
            if ¬(← body.isClosed) then body.close
          st := { st with machine := st.machine.abandonOutgoingBody }
          st := st.mapInFlight ({ · with
            pendingRequestBody := none
            waitingForContinue := false
            continueDeadline := none
          })

        if let some body := st.responseStream then
          if let some length := head.getSize false then
            Body.setKnownSize body (some length)

        if let some pending := st.currentRequest then
          if let some incoming := st.responseStream then
            pending.onResponse { line := head, body := incoming, extensions := Extensions.empty }

    | .closeBody =>
      if let some body := st.responseStream then
        if ¬(← Body.isClosed body) then Body.close body
      st := st.mapInFlight fun flight =>
        { flight with responseStream := none, responseComplete := true }

      -- Drop the rest of the request body: the producer is told it is done and the writer
      -- completes, rather than pumping into a peer that has stopped reading.
      if st.machine.peerWillNotReadBody then
        if let some body := st.requestBody then
          if ¬(← body.isClosed) then body.close
        if let some body := st.pendingRequestBody then
          if ¬(← body.isClosed) then body.close
        st := { st with machine := st.machine.abandonOutgoingBody }
        st := st.mapInFlight fun flight =>
          { flight with
            requestBody := none
            pendingRequestBody := none
            waitingForContinue := false
            continueDeadline := none
          }

    | .next =>
      -- Reset all per-request state for the next pipelined request, including the effective
      -- config: the next request's overrides must apply to the connection config, not to the
      -- one the finished request left behind.
      if let some pending := st.currentRequest then
        pending.onComplete
      closeAllRequestState st
      st := { st with
        inFlight := none
        requestDeadline := none
        config := baseConfig
        keepAliveTimeout := some baseConfig.keepAliveTimeout.val
        currentTimeout := baseConfig.keepAliveTimeout.val
      }

    | .failed err =>
      let clientErr : Error := .protocol err
      if let some pending := st.currentRequest then
        pending.onError clientErr

      if let some body := st.responseStream then
        if ¬(← Body.isClosed body) then body.closeWithError clientErr.toIOError
      sawFailure := true

    | .«continue» => pure ()

    | .close =>
      -- `.close` means the machine will carry no further message, so stop accepting requests
      -- before reporting this exchange complete. A caller that learns the exchange finished (a
      -- redirect chain deciding where to send its next hop) then cannot queue onto a connection
      -- that is on its way out.
      discard <| EIO.toBaseIO requestChannel.close
      if let some flight := st.inFlight then
        if flight.responseComplete then
          flight.pending.onComplete

  return (st, sawFailure)

/--
Terminal transition applied when a caller-facing problem forces the connection
to end (request timeout, shutdown signal, response body limit exceeded).
Rejects any in-flight request, closes all per-request resources, and parks
the H1 machine.
-/
private def abortState (state : ConnectionState) (err : Error) : Async ConnectionState := do
  if let some flight := state.inFlight then
    if flight.responseComplete then
      flight.pending.onComplete
    else
      flight.pending.onError err

  -- Close the response stream with the error so that a caller blocked in
  -- `readAll` receives a thrown exception rather than a silent short read.
  if let some body := state.responseStream then
    if ¬(← Body.isClosed body) then body.closeWithError err.toIOError

  closeAllRequestState state
  return { state with
    machine := state.machine.shutdown
    inFlight := none
    requestDeadline := none
  }

/--
Pure transition for a new request that has already had its known body
size resolved and its response stream allocated by the async caller.
-/
private def onNewRequest
    (pending : PendingRequest) (knownSize : Option Body.Length)
    (responseStream : Body.Stream) (requestConfig : Config) (deadline : Timestamp)
    (continueDeadline : Timestamp) (state : ConnectionState) : ConnectionState :=
  let machine := state.machine.sendRequest pending.request.line knownSize
  { state with
    machine
    config := requestConfig
    currentTimeout := requestConfig.readTimeout.val
    keepAliveTimeout := none
    requestDeadline := some deadline
    inFlight := some <|
      InFlightState.ofPending pending responseStream continueDeadline machine.awaitsContinue
  }

/--
Transition for a `.bodyInterest true` event: pulls the next chunk out of
the H1 machine, enforces `maxResponseBodySize`, and publishes the chunk.
-/
private def onBodyInterest (state : ConnectionState) : Async ConnectionState := do
  let (newMachine, pulledChunk) := state.machine.pullBody
  let mut st := { state with machine := newMachine }

  if let some pulled := pulledChunk then
    match state.config.maxResponseBodySize with
    | some maxSize => do
      let chunkSize : UInt64 := pulled.chunk.data.size.toUInt64
      let prevBytes : UInt64 := st.inFlight.map (·.downloadBodyBytes) |>.getD 0
      let newBodyBytes : UInt64 := prevBytes + chunkSize
      st := st.mapInFlight ({ · with downloadBodyBytes := newBodyBytes })
      if newBodyBytes > maxSize.toUInt64 then
        let err : Error := .bodyLimitExceeded
        if let some body := st.responseStream then
          if ¬(← Body.isClosed body) then body.closeWithError err.toIOError
        return ← abortState (st.mapInFlight ({ · with responseStream := none })) err
    | none => pure ()

    if let some body := st.responseStream then
      try body.send pulled.chunk pulled.incomplete catch _ => pure ()

      if pulled.final then
        if ¬(← Body.isClosed body) then Body.close body
        st := st.mapInFlight ({ · with responseStream := none, responseComplete := true })

  return st

/--
Processes a single async I/O event, returning the updated state and a `shouldClose` flag
that tells the main loop to exit.
-/
private def handleRecvEvent (baseConfig : Config) (state : ConnectionState) :
    Recv → Async (ConnectionState × Bool)
  | .bytes (some bytes) => do
    return ({ state with machine := state.machine.feed bytes }, false)

  | .bytes none => do

    -- Signal EOF to the machine so it can finish parsing any buffered data.
    -- The end-of-loop `machine.exhausted` guard will exit
    -- the loop once the machine drains; do NOT set shouldClose here or we skip
    -- the Phase 2/3 drain that delivers the final body chunk to the caller.
    return ({ state with machine := state.machine.noMoreInput }, false)

  | .requestBody (some chunk) => do
    return ({ state with machine := state.machine.sendData #[chunk] }, false)

  | .requestBody none => do
    if let some body := state.requestBody then
      if ¬(← body.isClosed) then body.close

    let st := { state with machine := state.machine.userClosedBody }
    return (st.mapInFlight ({ · with requestBody := none }), false)

  | .bodyInterest interested => do
    return (← if interested then onBodyInterest state else pure state, false)

  | .request (some pending) => do
    try
      let knownSize ← pending.request.body.getKnownSize
      let responseStream ← Body.mkStream
      let requestConfig := pending.requestOverrides.apply baseConfig
      let now ← Timestamp.now
      let deadline := now + requestConfig.requestTimeout.val
      let continueDeadline := now + requestConfig.expectContinueTimeout.val
      return (onNewRequest pending knownSize responseStream requestConfig deadline continueDeadline
        state, false)
    catch e =>
      pending.onError (.io e)
      return (state, false)

  | .request none => do
    return (state, true)

  | .close => do
    return (state, true)

  | .timeout => do
    return (← abortState state .timeout, true)

  | .continueTimeout => do
    -- The server never answered the expectation; send the body as if it had said `100 Continue`.
    -- Guarded so a fired timer can never clear a body the interim response already released.
    if state.waitingForContinue then
      return (state.mapInFlight (·.releasePendingBody), false)
    else
      return (state, false)

  | .shutdown => do
    return (← abortState state (.closed "connection shutdown"), true)

/--
Runs the main request/response processing loop for a single connection, as the background task
behind `Connection.new`. Drives the HTTP/1.1 state machine through four phases each iteration:
close finished readers, send buffered output, process H1 events, poll for I/O.
-/
private def run
    [Transport α]
    (socket : α)
    (machine : H1.Machine .sending)
    (config : Config)
    (connectionContext : CancellationContext)
    (requestChannel : Std.CloseableChannel PendingRequest) : Async Unit := do
  let mut state : ConnectionState := {
    machine := machine
    config := config
    currentTimeout := config.keepAliveTimeout.val
    keepAliveTimeout := some config.keepAliveTimeout.val
    expectData := none
    inFlight := none
  }

  -- The loop body runs user-supplied `Body` implementations (body pumps, `getKnownSize`,
  -- `close`); an exception escaping the loop must not skip the cleanup below, which fails the
  -- in-flight request and closes the request channel and socket — otherwise callers awaiting
  -- the response would hang forever.
  try
    while ¬state.machine.halted do

      -- Phase 1: close any reader that the user has signaled is done. `isClosed` cannot tell a
      -- body the caller finished from one that failed, and ending the framing of a failed body
      -- would hand the peer a truncated request that looks complete, so pull once: `recv` on a
      -- closed body re-raises the error it was closed with.
      if let some body := state.requestBody then
        let closed? ← try
          if ← body.isClosed then
            discard <| body.recv
            pure (some true)
          else
            pure (some false)
        catch e =>
          state ← abortState state (.io e)
          pure none
        let some closed := closed? | break
        if closed then
          let newState := { state with machine := state.machine.userClosedBody }
          state := newState.mapInFlight fun flight => { flight with requestBody := none }

      let responseBodyClosed ← match state.responseStream with
        | some body => Body.isClosed body
        | none => pure true

      if responseBodyClosed then
        state := { state with machine := state.machine.drainBody }

      -- Phase 2: advance the state machine and flush any output.
      let (newMachine, step) := state.machine.step
      state := { state with machine := newMachine }

      if step.output.size > 0 then
        try Transport.sendAll socket #[step.output.toByteArray]
        catch _ =>
          state ← abortState state (.closed "connection write failed")
          break

      -- Phase 3: process all events emitted by this step.
      let (newState, sawFailure) ← processH1Events config requestChannel step.events state

      state := newState

      if sawFailure then
        break

      -- Phase 4: wait for the next IO event.
      -- Skip if the machine has already halted or if the transport is closed and
      -- there is nothing left to wait for (no body to consume, no new requests).
      if state.machine.exhausted then
        break

      if state.waitingOnIO then
        state := { state with requiresData := false }
        let event ← pollNextEvent socket requestChannel connectionContext state
        let (newState, shouldClose) ← handleRecvEvent config state event
        state := newState
        if shouldClose then break

      if state.machine.exhausted then
        break

  catch e =>
    try
      state ← abortState state (.io e)
    catch _ =>
      pure ()

  -- Clean up: notify any in-flight request and close all open streams.
  try discard <| abortState state (.closed "connection closed")
  catch _ => pure ()

  discard <| EIO.toBaseIO requestChannel.close

  -- Drain any remaining queued requests.
  repeat do
    match ← requestChannel.tryRecv with
    | some pending => pending.onError (.closed "connection closed")
    | none => break

  Transport.close socket

/--
Queues a request and awaits its response, together with a completion promise that
resolves when the connection is ready for the next request.

Failures are reported as a typed `Client.Error` so callers (e.g. the pool's retry
policy) can distinguish connection-level failures from application-level ones.
-/
def sendTracked (connection : Connection) (request : Request Body.Any)
    (requestOverrides : RequestOverrides := {}) :
    Async (Except Error (Response Body.Stream × IO.Promise (Except Error Unit))) := do
  let responsePromise ← IO.Promise.new
  let completionPromise ← IO.Promise.new

  let task ← connection.requestChannel.send
    { request, responsePromise, completionPromise, requestOverrides }

  let .ok _ ← await task
    | return .error (.closed "connection closed before request could be sent")

  match ← await responsePromise.result! with
  | .ok response => return .ok (response, completionPromise)
  | .error e => return .error e

/--
Queues a request and awaits its response.
Use `sendTracked` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (connection : Connection) (request : Request β)
    (requestOverrides : RequestOverrides := {}) : Async (Response Body.Stream) := do
  let sent ← connection.sendTracked { request with } requestOverrides
  let (response, _) ← Error.throwOrPure sent
  return response

/--
`true` once the connection can no longer accept requests: its request channel was closed, either by
`close` or by the background loop shutting down (server EOF, idle timeout, protocol error). Any
subsequent `send` fails immediately.
-/
def isClosed (connection : Connection) : BaseIO Bool :=
  connection.requestChannel.isClosed

/--
Waits for the background loop to exit.
-/
def waitShutdown (connection : Connection) : Async Unit :=
  await connection.shutdown

/--
Closes the connection: cancels the background loop's context (aborting any in-flight exchange) and
closes the request channel so queued and future sends fail promptly.
-/
def close (connection : Connection) : Async Unit := do
  connection.context.cancel .shutdown
  discard <| EIO.toBaseIO connection.requestChannel.close

/--
Creates an HTTP client connection over the given transport and starts its background loop.
The transport type `t` is used only during construction and is not stored in `Connection`.
-/
def new [Transport t] (client : t) (config : Config := {}) : Async Connection := do
  let requestChannel ← Std.CloseableChannel.new
  let shutdown ← IO.Promise.new
  let context ← CancellationContext.new
  let machine : H1.Machine .sending := { config := config.toH1Config }

  background do
    try
      run client machine config context requestChannel
    finally
      discard <| shutdown.resolve ()

  pure { requestChannel, shutdown, config, context }

end Std.Http.Client.Connection
