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
  or when the exchange fails after the response headers have been delivered.
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
Closes `body` when it is present. `Body.close` is idempotent, so no `isClosed` test guards it: such
a test could not be atomic with the close, and the window between the two is exactly when a
concurrent close lands.
-/
private def closeBody [Body β] (body : Option β) : Async Unit :=
  body.forM Body.close

/--
Stops the connection from accepting further requests. The channel is closed from three racing paths
— the machine's `.close` event, the loop's cleanup, and `Connection.close` — and
`CloseableChannel.close` throws on a second close, so an already-closed channel is the expected
case here rather than an error. Testing `isClosed` first would not be enough: two callers can both
observe an open channel and both proceed to close it, so the second close is swallowed instead.
-/
private def stopAcceptingRequests (requestChannel : Std.CloseableChannel PendingRequest) :
    IO Unit := do
  try requestChannel.close catch _ => pure ()

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
  Set once the caller's response stream has been seen closed. `interestSelector` answers `false`
  immediately for the rest of the stream's life, so polling it again would spin the loop; from here
  on the body is drained by the loop instead.
  -/
  responseStreamAbandoned : Bool := false

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
Clears the `Expect: 100-continue` bookkeeping: the parked body and the wait state that goes with it.
Leaves `requestBody` alone; the two transitions below decide what the writer pump sends next.
-/
def clearContinue (s : InFlightState) : InFlightState :=
  { s with pendingRequestBody := none, waitingForContinue := false, continueDeadline := none }

/--
Releases a body parked behind `Expect: 100-continue` so the writer pump starts sending it.
-/
def releasePendingBody (s : InFlightState) : InFlightState :=
  { s.clearContinue with requestBody := s.pendingRequestBody }

/--
Clears both request body handles, so nothing is left for the writer pump to send.
-/
def dropOutgoingBody (s : InFlightState) : InFlightState :=
  { s.clearContinue with requestBody := none }

/--
Closes both handles on the outgoing body: the one the writer pump is consuming and the one parked
behind `Expect: 100-continue`. Idempotent.
-/
def closeRequestBodies (s : InFlightState) : Async Unit := do
  closeBody s.requestBody
  closeBody s.pendingRequestBody

/--
Ends the exchange successfully: reports completion to the caller and closes every resource tied to
it. Idempotent.
-/
def complete (s : InFlightState) : Async Unit := do
  s.pending.onComplete
  s.closeRequestBodies
  closeBody s.responseStream

/--
Ends the exchange with `err`: resolves the caller's promises, fails the response stream so a caller
blocked in `readAll` receives a thrown exception rather than a silent short read, and closes every
resource tied to the exchange. A failure that lands after the caller already holds the whole body
ends the *connection*, not the exchange, so the request is reported complete instead. Idempotent.

No `isClosed` test guards the stream failure: every path that hands the caller a complete body
clears `responseStream` first, so a stream still recorded here is one that never finished, and
failing it is right whether or not the caller has already walked away. An `isClosed` test would make
that outcome depend on whether the caller's `close` happened to land inside the gap between the test
and the call.
-/
def reject (s : InFlightState) (err : Error) : Async Unit := do
  if s.responseComplete then
    s.pending.onComplete
  else
    s.pending.onError err
  s.responseStream.forM (·.closeWithError err.toIOError)
  s.closeRequestBodies

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
Socket inactivity bound for the next blocking wait: the idle keep-alive gap while parked between
requests, the read timeout while an exchange is running. Derived rather than stored so it cannot
drift out of step with `config`, which already carries the in-flight request's overrides.
-/
@[inline]
def socketTimeout (s : ConnectionState) : Millisecond.Offset :=
  if s.waitingForRequest then s.config.keepAliveTimeout.val else s.config.readTimeout.val

/--
Applies `f` to the current in-flight state, if any.
-/
@[inline]
def mapInFlight (s : ConnectionState) (f : InFlightState → InFlightState) : ConnectionState :=
  { s with inFlight := s.inFlight.map f }

/--
Returns the connection to idle. `requestDeadline` bounds the in-flight exchange, so it is cleared
here rather than at each call site, where forgetting it would leave a fired timer aborting the
*next* request.
-/
@[inline]
def clearInFlight (s : ConnectionState) : ConnectionState :=
  { s with inFlight := none, requestDeadline := none }

/--
The request body currently being pumped to the wire, if any.
-/
@[inline]
def requestBody (s : ConnectionState) : Option Body.Any :=
  s.inFlight.bind (·.requestBody)

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
  s.inFlight.any (·.waitingForContinue)

/--
The deadline at which a body parked behind `Expect: 100-continue` is sent regardless.
-/
@[inline]
def continueDeadline (s : ConnectionState) : Option Timestamp :=
  s.inFlight.bind (·.continueDeadline)

/--
`true` once the caller's response stream has been seen closed.
-/
@[inline]
def responseStreamAbandoned (s : ConnectionState) : Bool :=
  s.inFlight.any (·.responseStreamAbandoned)

/--
`true` when the response body parsed so far already exceeds `maxResponseBodySize`.

The machine counts every body byte it decodes, whether the caller pulled it or the loop discarded
it, so a caller that walks away from its response stream cannot drain past the limit unnoticed.
-/
@[inline]
def exceedsBodyLimit (s : ConnectionState) : Bool :=
  match s.config.maxResponseBodySize with
  | some maxSize => s.machine.bodyBytesRead > maxSize
  | none => false

/--
`true` when the loop depends on an external event to advance. Those events are exactly the sources
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
Stops sending the request body: closes both body handles and ends the outgoing message where it
stands. Used when the peer answers before the body was sent, which is both how an `Expect:
100-continue` is refused and how a server cuts a request short.
-/
private def abandonRequestBody (state : ConnectionState) : Async ConnectionState := do
  state.inFlight.forM (·.closeRequestBodies)
  return { state with machine := state.machine.abandonOutgoingBody }
    |>.mapInFlight (·.dropOutgoingBody)

/--
Records that the outgoing body producer is done: ends the outgoing message and drops the handle the
writer pump was consuming.
-/
private def finishRequestBody (state : ConnectionState) : ConnectionState :=
  { state with machine := state.machine.userClosedBody }
    |>.mapInFlight ({ · with requestBody := none })

/--
Ends the caller-facing response body: closes the stream and marks the response complete, so a later
connection failure is reported to the caller as a completion rather than an error.
-/
private def finishResponseBody (state : ConnectionState) : Async ConnectionState := do
  closeBody state.responseStream
  return state.mapInFlight ({ · with responseStream := none, responseComplete := true })

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
  -- Every deadline armed below is measured against this one instant, so the timers racing in a
  -- single poll cannot disagree about what "now" is.
  let now ← Timestamp.now
  let remaining (deadline : Timestamp) : Millisecond.Offset := (deadline - now).toMilliseconds

  let mut selectables : Array (Selectable Recv) := #[
    .case connectionContext.doneSelector (fun _ => pure .shutdown)
  ]

  -- Each timeout below is armed exactly when its own precondition holds, never conditioned on which
  -- other sources happen to be active: whether a bound is enforced must not depend on the phase the
  -- machine is in when the loop happens to park.

  if state.machine.needsInput then
    selectables := selectables.push
      (.case (← Selector.sleep state.socketTimeout) (fun _ => pure .timeout))

    let expectedBytes := state.expectData
      |>.getD state.config.defaultRequestBufferSize
      |>.min state.config.maxRecvChunkSize
      |>.toUInt64

    selectables := selectables.push
      (.case (Transport.recvSelector socket expectedBytes) (fun bytes => pure (Recv.bytes bytes)))

  -- `requestTimeout` bounds the whole exchange, so it stays armed for as long as one is in
  -- flight — including while the loop is parked on the caller's request body or waiting for the
  -- caller to read the response, neither of which touches the socket.
  if let some deadline := state.requestDeadline then
    selectables := selectables.push
      (.case (← Selector.sleep (remaining deadline)) (fun _ => pure .timeout))

  if let some requestBody := state.requestBody then
    selectables := selectables.push
      (.case requestBody.recvSelector (pure <| Recv.requestBody ·))

  -- RFC 9110 §10.1.1: a server may ignore `Expect: 100-continue` entirely, so the wait for the
  -- interim response is bounded; on expiry the body is sent as if `100 Continue` had arrived.
  -- `continueDeadline` is set exactly while `waitingForContinue` holds.
  if let some deadline := state.continueDeadline then
    selectables := selectables.push
      (.case (← Selector.sleep (remaining deadline)) (fun _ => pure .continueTimeout))

  if state.waitingForRequest then
    selectables := selectables.push
      (.case requestChannel.recvSelector (pure <| .request ·))

  -- The response stream is dropped from the poll only once a `.bodyInterest false` has reported it
  -- closed: that report is itself the wake-up, so nothing is lost, whereas a closedness test here
  -- would drop the body exactly when `close` lands in the gap, parking the loop with no source that
  -- can ever wake the drainable body.
  if state.machine.canPullBodyNow ∧ ¬state.responseStreamAbandoned then
    if let some responseBody := state.responseStream then
      selectables := selectables.push
        (.case responseBody.interestSelector (pure <| .bodyInterest ·))

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
  let mut state := state
  let mut sawFailure := false

  for event in events do
    match event with
    | .needAnswer | .«continue» =>
      pure ()

    | .needMoreData expectData =>
      state := { state with requiresData := true, expectData }

    | .endHeaders head =>
      if head.status.isInformational then
        if head.status == .continue && state.waitingForContinue then
          state := state.mapInFlight (·.releasePendingBody)
      else
        if state.waitingForContinue then
          state ← abandonRequestBody state

        if let some flight := state.inFlight then
          if let some incoming := flight.responseStream then
            if let some length := head.getSize false then
              Body.setKnownSize incoming (some length)
            flight.pending.onResponse
              { line := head, body := incoming, extensions := Extensions.empty }

    | .closeBody =>
      state ← finishResponseBody state

      -- Drop the rest of the request body: tell the producer it is done and complete the writer
      -- rather than pump into a peer that has stopped reading.
      if state.machine.peerWillNotReadBody then
        state ← abandonRequestBody state

    | .next =>
      -- Reset all per-request state for the next pipelined request, including the effective
      -- config: the next request's overrides must apply to the connection config, not to the
      -- one the finished request left behind.
      state.inFlight.forM (·.complete)
      state := { state.clearInFlight with config := baseConfig }

    | .failed err =>
      -- The closed channel is what tells the pool this connection is spent.
      state.inFlight.forM (·.reject (.protocol err))
      sawFailure := true

    | .close =>
      -- `.close` means the machine will carry no further message, so stop accepting requests
      -- before reporting this exchange complete. A caller that learns the exchange finished (a
      -- redirect chain deciding where to send its next hop) then cannot queue onto a connection
      -- that is on its way out.
      stopAcceptingRequests requestChannel
      if let some flight := state.inFlight then
        if flight.responseComplete then
          flight.pending.onComplete

  return (state, sawFailure)

/--
Terminal transition applied when a caller-facing problem forces the connection
to end (request timeout, shutdown signal, response body limit exceeded).
Rejects any in-flight request, closes all per-request resources, and parks
the H1 machine.
-/
private def abortState (state : ConnectionState) (err : Error) : Async ConnectionState := do
  state.inFlight.forM (·.reject err)
  return { state.clearInFlight with machine := state.machine.shutdown }

/--
Pure transition for a new request that has already had its known body
size resolved and its response stream allocated by the async caller.
-/
private def startRequest
    (pending : PendingRequest) (knownSize : Option Body.Length)
    (responseStream : Body.Stream) (requestConfig : Config) (deadline : Timestamp)
    (continueDeadline : Timestamp) (state : ConnectionState) : ConnectionState :=
  let machine := state.machine.sendRequest pending.request.line knownSize

  { state with
    machine
    config := requestConfig
    requestDeadline := some deadline
    inFlight := some <|
      InFlightState.ofPending pending responseStream continueDeadline machine.awaitsContinue
  }

/--
Transition for a `.bodyInterest true` event: pulls the next chunk out of the H1 machine, enforces
`maxResponseBodySize`, and publishes the chunk. The `shouldClose` flag reports the size limit, the
one outcome here that ends the connection; a send onto a stream the caller closed under us is not an
error, since the loop drains the rest of the body itself.
-/
private def pullResponseBody (state : ConnectionState) : Async (ConnectionState × Bool) := do
  let (newMachine, pulledChunk) := state.machine.pullBody
  let mut state := { state with machine := newMachine }

  if let some pulled := pulledChunk then
    if state.exceedsBodyLimit then
      return (← abortState state .bodyLimitExceeded, true)

    if let some body := state.responseStream then
      try body.send pulled.chunk pulled.incomplete catch _ => pure ()

      if pulled.final then
        state ← finishResponseBody state

  return (state, false)

/--
Processes a single async I/O event, returning the updated state and a `shouldClose` flag
that tells the main loop to exit.
-/
private def handleRecvEvent (baseConfig : Config) (state : ConnectionState) :
    Recv → Async (ConnectionState × Bool)
  | .bytes (some bytes) =>
    pure ({ state with machine := state.machine.feed bytes }, false)

  | .bytes none =>
    pure ({ state with machine := state.machine.noMoreInput }, false)

  | .requestBody (some chunk) =>
    pure ({ state with machine := state.machine.sendData #[chunk] }, false)

  | .requestBody none => do
    closeBody state.requestBody
    return (finishRequestBody state, false)

  | .bodyInterest interested => do
    if interested then
      pullResponseBody state
    else
      return (state.mapInFlight ({ · with responseStreamAbandoned := true }), false)

  | .request (some pending) => do
    try
      let knownSize ← pending.request.body.getKnownSize
      let responseStream ← Body.mkStream
      let requestConfig := pending.requestOverrides.apply baseConfig
      let now ← Timestamp.now
      let deadline := now + requestConfig.requestTimeout.val
      let continueDeadline := now + requestConfig.expectContinueTimeout.val
      return (startRequest pending knownSize responseStream requestConfig deadline continueDeadline
        state, false)
    catch e =>
      pending.onError (.io e)
      return (state, false)

  | .request none | .close =>
    pure (state, true)

  | .timeout => do
    return (← abortState state .timeout, true)

  | .continueTimeout =>
    -- The server never answered the expectation; send the body as if it had said `100 Continue`.
    -- Guarded so a fired timer can never clear a body the interim response already released.
    if state.waitingForContinue then
      pure (state.mapInFlight (·.releasePendingBody), false)
    else
      pure (state, false)

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
    machine, config
    expectData := none
    inFlight := none
  }

  try
    -- `exhausted` subsumes `halted`, and also stops the loop once the transport is at EOF with no
    -- buffered body left, which would otherwise spin with no source able to wake it.
    while ¬state.machine.exhausted do
      -- Phase 1: end the outgoing message once the caller's body producer is done. A user-supplied
      -- body may raise from `isClosed`, and framing a failed body would hand the peer a truncated
      -- request that looks complete, so a raise aborts the exchange instead.

      if let some body := state.requestBody then
        let closed : Except IO.Error Bool ← try .ok <$> body.isClosed catch e => pure (.error e)
        match closed with
        | .error e =>
          state ← abortState state (.io e)
          break
        | .ok closed =>
          if closed then
            state := finishRequestBody state

      -- The machine may drain the response body only once the caller's stream is gone or closed.
      -- Those bytes bypass `pullResponseBody`, so the limit is checked here too: abandoning the
      -- response stream must not be a way out of `maxResponseBodySize`.
      if (← state.responseStream.mapM Body.isClosed).getD true then
        state := { state with machine := state.machine.drainBody }

        if state.exceedsBodyLimit then
          state ← abortState state .bodyLimitExceeded
          break

      -- Phase 2: advance the state machine and flush any output.

      let (newMachine, step) := state.machine.step
      state := { state with machine := newMachine }

      if step.output.size > 0 then
        try Transport.sendAll socket step.output.data
        catch _ =>
          state ← abortState state (.closed "connection write failed")
          break

      -- Phase 3: process all events emitted by this step.

      let (newState, sawFailure) ← processH1Events config requestChannel step.events state
      state := newState

      if sawFailure ∨ state.machine.exhausted then
        break

      -- Phase 4: wait for the next IO event. Skipped when the last step left buffered work behind,
      -- since then there is nothing to wait for.

      if state.waitingOnIO then
        state := { state with requiresData := false }
        let event ← pollNextEvent socket requestChannel connectionContext state
        let (newState, shouldClose) ← handleRecvEvent config state event
        state := newState
        if shouldClose then break

  catch e =>
    try state ← abortState state (.io e) catch _ => pure ()

  -- Clean up: notify any in-flight request and close all open streams.
  try discard <| abortState state (.closed "connection closed") catch _ => pure ()

  stopAcceptingRequests requestChannel

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
  stopAcceptingRequests connection.requestChannel

/--
Creates an HTTP client connection over the given transport and starts its background loop.
The transport type `t` is used only during construction and is not stored in `Connection`.
-/
def new [Transport t] (client : t) (config : Config := {}) : Async Connection := do
  let requestChannel ← Std.CloseableChannel.new
  let shutdown ← IO.Promise.new
  let context ← CancellationContext.new

  background do
    try
      run client { config := config.toH1Config } config context requestChannel
    finally
      shutdown.resolve ()

  pure { requestChannel, shutdown, config, context }

end Std.Http.Client.Connection
