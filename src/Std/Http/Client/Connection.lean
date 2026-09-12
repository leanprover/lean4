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
public import Std.Http.Client.Error
public import Std.Http.Client.Authenticator
public import Std.Http.Client.CookieHandler
public import Std.Http.Client.Proxy

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
A response whose head has arrived, paired with the promise reporting how its exchange ended.
-/
structure TrackedResponse where
  /--
  The response as the peer sent it. Its body is still streaming while the exchange runs.
  -/
  response : Response Body.Stream

  /--
  Resolves when the connection has finished the exchange and is ready for the next request, or with
  the failure that ended it after the head was delivered.
  -/
  completion : IO.Promise (Except Error Unit)

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
  The origin this connection was opened for. Requests sent on it are addressed to this origin, and
  it is the origin the `CookieHandler` and `Authenticator` are consulted about.
  -/
  origin : URI.Origin

  /--
  Where this connection's transport actually goes, as chosen by `Config.proxySelector` for `origin`.
  Requests are sent in absolute-form while it is a proxy.
  -/
  proxy : Proxy

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
  | bytes (data : Option ByteArray)
  | requestBody (chunk : Option Chunk)
  | bodyInterest (interested : Bool)
  | request (pending : Option PendingRequest)
  | timeout
  | continueTimeout
  | shutdown
  | close
  /--
  A source in the poll raised. `Selectable.one` reports the failure without naming the source it
  came from, so the error is carried as a value and attributed by the handler rather than assumed
  to be the transport's.
  -/
  | failed (error : IO.Error)

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
    (continueDeadline : Timestamp) (awaitsContinue : Bool) : InFlightState :=
  let body := some pending.request.body
  { pending
    responseStream := some responseStream
    waitingForContinue := awaitsContinue
    requestBody := if awaitsContinue then none else body
    pendingRequestBody := if awaitsContinue then body else none
    continueDeadline := if awaitsContinue then some continueDeadline else none }

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
The caller's response stream while the machine holds body bytes it can hand over, i.e. exactly while
the loop's next move is the caller's to make: what the poll waits on, and what stands the socket
inactivity bound down, since no byte from the peer is needed to advance.
-/
@[inline]
def pullableResponseStream (s : ConnectionState) : Option Body.Stream :=
  if s.machine.canPullBodyNow ∧ ¬s.responseStreamAbandoned then s.responseStream else none

/--
`true` while the loop's next move is the caller's to make: the machine holds transport bytes it has
not consumed and a response stream the caller still owns to decode them into, so it can advance
without another byte from the peer.
-/
@[inline]
def awaitsBodyPull (s : ConnectionState) : Bool :=
  s.pullableResponseStream.isSome ∧ s.machine.hasBufferedInput

/--
`true` while every wait the loop is parked on is the caller's rather than the peer's: it holds body
bytes the caller has not pulled, or it is waiting on the body the caller is still producing.
-/
@[inline]
def awaitsCaller (s : ConnectionState) : Bool :=
  s.awaitsBodyPull ∨ s.requestBody.isSome

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
Ends the outgoing message where it stands and lets go of both body handles without closing them.
Only for a body that raised: such a body has already closed itself, and the raise reaches the loop
on the producer's own thread while it still holds that body's lock, which `Mutex.atomically` is not
reentrant across. Every other caller wants `abandonRequestBody`, which closes what it drops.
-/
private def dropRequestBody (state : ConnectionState) : ConnectionState :=
  { state.mapInFlight (·.dropOutgoingBody) with
    machine := state.machine.abandonOutgoingBody }

/--
Stops sending the request body: closes both body handles and ends the outgoing message where it
stands. Used when the peer answers before the body was sent, which is both how an `Expect:
100-continue` is refused and how a server cuts a request short.
-/
private def abandonRequestBody (state : ConnectionState) : Async ConnectionState := do
  state.inFlight.forM (·.closeRequestBodies)
  return dropRequestBody state

/--
Records that the outgoing body producer is done: ends the outgoing message and drops the handle the
writer pump was consuming.
-/
private def finishRequestBody (state : ConnectionState) : ConnectionState :=
  { state.mapInFlight ({ · with requestBody := none }) with
    machine := state.machine.userClosedBody }

/--
Ends the caller-facing response body: closes the stream and marks the response complete, so a later
connection failure is reported to the caller as a completion rather than an error.
-/
private def finishResponseBody (state : ConnectionState) : Async ConnectionState := do
  closeBody state.responseStream
  return state.mapInFlight ({ · with responseStream := none, responseComplete := true })

/--
Waits for the next I/O event across all sources relevant to `state`, racing every active selectable.
A source that raises is reported as `.failed`, carrying its error for the handler to attribute.
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

  let remaining deadline := (deadline - now).toMilliseconds

  let timer (expiry : Selector Unit) (event : Recv) : Selectable Recv :=
    .case expiry (fun _ => pure event)

  let mut selectables : Array (Selectable Recv) := #[
    .case connectionContext.doneSelector (fun _ => pure .shutdown)
  ]

  -- Each timeout below is armed exactly when its own precondition holds, never conditioned on which
  -- other sources happen to be active: whether a bound is enforced must not depend on the phase the
  -- machine is in when the loop happens to park.

  if state.machine.needsInput then

    unless state.awaitsCaller do
      selectables := selectables.push (timer (← Selector.sleep state.socketTimeout) .timeout)

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
    selectables := selectables.push (timer (← Selector.sleep (remaining deadline)) .timeout)

  if let some requestBody := state.requestBody then
    selectables := selectables.push
      (.case requestBody.recvSelector (pure <| Recv.requestBody ·))

  -- RFC 9110 §10.1.1: a server may ignore `Expect: 100-continue` entirely, so the wait for the
  -- interim response is bounded; on expiry the body is sent as if `100 Continue` had arrived.
  -- `continueDeadline` is set exactly while `waitingForContinue` holds.
  if let some deadline := state.continueDeadline then
    selectables := selectables.push
      (timer (← Selector.sleep (remaining deadline)) .continueTimeout)

  if state.waitingForRequest then
    selectables := selectables.push
      (.case requestChannel.recvSelector (pure <| .request ·))

  -- The response stream is dropped from the poll only once a `.bodyInterest false` has reported it
  -- closed: that report is itself the wake-up, so nothing is lost, whereas a closedness test here
  -- would drop the body exactly when `close` lands in the gap, parking the loop with no source that
  -- can ever wake the drainable body.
  if let some responseBody := state.pullableResponseStream then
    selectables := selectables.push
      (.case responseBody.interestSelector (pure <| .bodyInterest ·))

  try Selectable.one selectables catch e => pure (.failed e)

/--
The size to publish on the stream handed to the caller for a response to `method`.

RFC 9112 §6.3 ends a HEAD response, and any 1xx, 204, or 304, at the header block whatever framing
fields it carries: their `Content-Length` describes the content the equivalent `GET` would return,
not bytes on this connection. The machine frames them as empty, so the head's own size must not be
republished here — a caller sizing a buffer off `getKnownSize` would wait for content that never
comes.
-/
private def responseBodySize (method : Method) (head : Response.Head) : Option Body.Length :=
  let bodyless :=
    method == .head ∨ head.status.isInformational ∨ head.status == .noContent ∨
      head.status == .notModified
  if bodyless then some (.fixed 0)
  else H1.Message.Head.getSize (dir := .sending) head (allowEOFBody := false)

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
      if head.status.isInterim then
        if head.status == .continue && state.waitingForContinue then
          state := state.mapInFlight (·.releasePendingBody)
      else
        if state.waitingForContinue then
          state ← abandonRequestBody state

        if let some flight := state.inFlight then
          if let some incoming := flight.responseStream then
            Body.setKnownSize incoming (responseBodySize flight.pending.request.line.method head)
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
Hands a pulled chunk to the caller's response stream, bounded by the exchange deadline and by the
connection's cancellation. Reports the failure that ended the wait, or `none` once the chunk is the
caller's.
-/
private def deliverResponseChunk
    (connectionContext : CancellationContext) (deadline : Option Timestamp)
    (body : Body.Stream) (pulled : H1.PulledChunk) : Async (Option Error) := do
  let handed ← try body.trySend pulled.chunk pulled.incomplete catch _ => pure true
  if handed then
    return none

  let parked : Std.CloseableChannel Unit ← Std.CloseableChannel.new

  background do
    try body.send pulled.chunk pulled.incomplete catch _ => pure ()
    try parked.close catch _ => pure ()

  let mut selectables : Array (Selectable (Option Error)) := #[
    .case parked.recvSelector (fun _ => pure none),
    .case connectionContext.doneSelector (fun _ => pure (some (.closed "connection shutdown")))
  ]

  if let some deadline := deadline then
    let now ← Timestamp.now
    selectables := selectables.push
      (.case (← Selector.sleep (deadline - now).toMilliseconds) (fun _ => pure (some .timeout)))

  try Selectable.one selectables catch e => pure (some (.io e))

/--
Transition for a `.bodyInterest true` event: pulls the next chunk out of the H1 machine, enforces
`maxResponseBodySize`, and hands the chunk to the caller. The `shouldClose` flag reports the two
outcomes here that end the connection: the size limit, and a hand-over that outlived the exchange.
-/
private def pullResponseBody (connectionContext : CancellationContext) (state : ConnectionState) :
    Async (ConnectionState × Bool) := do
  let (newMachine, pulledChunk) := state.machine.pullBody
  let mut state := { state with machine := newMachine }

  if let some pulled := pulledChunk then
    if state.exceedsBodyLimit then
      return (← abortState state .bodyLimitExceeded, true)

    if let some body := state.responseStream then
      if let some err ← deliverResponseChunk connectionContext state.requestDeadline body pulled then
        return (← abortState state err, true)

      if pulled.final then
        state ← finishResponseBody state

  return (state, false)

/--
Processes a single async I/O event, returning the updated state and a `shouldClose` flag
that tells the main loop to exit.
-/
private def handleRecvEvent (baseConfig : Config) (connectionContext : CancellationContext)
    (state : ConnectionState) : Recv → Async (ConnectionState × Bool)
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
      pullResponseBody connectionContext state
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

  | .failed error => do
    -- `Selectable.one` reports a raise without naming the source it came from, and of the sources
    -- in the poll only the caller's outgoing body can raise: the rest are timers, the request
    -- channel, and the transport, whose failure means the connection is gone. So the two are told
    -- apart by whether a body was being pumped — which is also what decides the classification. A
    -- request whose body was half-written cannot be replayed whoever it was that broke, so it ends
    -- as the caller's `.io` rather than as a retryable close, and the outgoing message ends where
    -- it stands rather than being framed as if the body had finished.
    if state.requestBody.isSome then
      return (← abortState (dropRequestBody state) (.io error), true)

    return (← abortState state (.closed s!"connection read failed: {error}"), true)

/--
Reconciles the machine with the two bodies the caller owns: the outgoing one it produces and the
incoming one it consumes. Reports whether the connection has to stop.

The outgoing message ends once the producer is done. `isClosed` is true for a producer that failed
just as it is for one that finished, so a closed body is probed with `tryRecv`, which raises the
terminal error a `closeWithError` recorded. Framing a failed body would hand the peer a truncated
request that looks complete, so a raise — from either call, both being user-supplied code — ends
the message where it stands and fails the exchange instead.
-/
private def closeFinishedBodies (state : ConnectionState) : Async (ConnectionState × Bool) := do
  let mut state := state

  if let some body := state.requestBody then
    let pulled : Except IO.Error (Option (Option Chunk)) ←
      try
        if ← body.isClosed then .ok <$> body.tryRecv else pure (.ok none)
      catch e => pure (.error e)
    match pulled with
    | .error e =>
      state ← abandonRequestBody state
      return (← abortState state (.io e), true)
    -- A chunk left buffered by a producer that has since gone away still belongs on the wire.
    | .ok (some (some chunk)) =>
      state := { state with machine := state.machine.sendData #[chunk] }
    | .ok (some none) =>
      state := finishRequestBody state
    | .ok none => pure ()

  -- The machine may drain the response body only once the caller's stream is gone or closed. Those
  -- bytes bypass `pullResponseBody`, so the limit is checked here too: abandoning the response
  -- stream must not be a way out of `maxResponseBodySize`.
  if (← state.responseStream.mapM Body.isClosed).getD true then
    state := { state with machine := state.machine.drainBody }

    if state.exceedsBodyLimit then
      return (← abortState state .bodyLimitExceeded, true)

  return (state, false)

/--
Runs the main request/response processing loop for a single connection, as the background task
behind `Connection.new`. Drives the HTTP/1.1 state machine through four phases each iteration:
close finished bodies, send buffered output, process H1 events, poll for I/O.
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
      -- Phase 1: settle the caller-owned bodies against the machine.

      let (newState, shouldClose) ← closeFinishedBodies state
      state := newState
      if shouldClose then break

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
        let (newState, shouldClose) ← handleRecvEvent config connectionContext state event
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
`true` once the connection can no longer accept requests: its request channel was closed, either by
`close` or by the background loop shutting down (server EOF, idle timeout, protocol error). Any
subsequent `send` fails immediately.
-/
def isClosed (connection : Connection) : BaseIO Bool :=
  connection.requestChannel.isClosed

/--
The port an absolute-form target names for `origin`, omitted when it is the scheme's default so the
target reads the way the origin itself is written.
-/
private def absoluteFormPort (origin : URI.Origin) : URI.Port :=
  if origin.port == URI.Scheme.defaultPort origin.scheme then .omitted else .value origin.port

/--
The form this connection sends `target` in: absolute-form while it goes through a proxy, which
RFC 9112 §3.2.2 requires there, and origin-form while it goes to the origin directly. Targets with
no path to re-address (authority-form, asterisk-form) are sent as they are.
-/
private def requestTargetFor (connection : Connection) (target : RequestTarget) : RequestTarget :=
  match connection.proxy, target with
  | .direct, .absoluteForm uri => .originForm uri.path uri.query
  | .http .., .originForm path query =>
    .absoluteForm {
      scheme := connection.origin.scheme
      authority := some {
        host := connection.origin.host
        port := absoluteFormPort connection.origin
      }
      path
      query
      fragment := none
    }
  | .direct, target | .http .., target => target

/--
Completes `request` against the connection it is about to be sent on: the request-target form the
transport requires, the `Host` of the origin unless the caller named one itself (RFC 9112 §3.2
requires the field, and only this layer knows the origin), and the cookies the configured handler
holds for this origin and target, joined with any the caller attached.
-/
private def prepareRequest (connection : Connection) (request : Request Body.Any) : Async (Request Body.Any) := do
  let target := connection.requestTargetFor request.line.uri
  let mut headers := request.line.headers

  if !headers.contains .host then
    headers := headers.insert .host (.ofString! connection.origin.hostHeader)

  if let some handler := connection.config.cookieHandler then
    let cookies :=
      (headers.getAll? .cookie).getD #[] ++
      (← handler.load connection.origin target)

    unless cookies.isEmpty do
      headers := (headers.erase .cookie).insert .cookie
        (.ofString! (String.intercalate "; " (cookies.toList.map (·.value))))

  return { request with line := { request.line with uri := target, headers } }

/--
The kind of authentication challenge `status` carries, if any.
-/
private def challengeKind? (status : Status) : Option Challenge.Kind :=
  if status == .unauthorized then some .server
  else if status == .proxyAuthenticationRequired then some .proxy
  else none

/--
`true` when an exchange ending in `head` leaves this connection able to carry another request: the
client allows reuse at all, the response did not ask for closure, and its body is framed by
something other than the connection close itself (RFC 9112 §6.3).
-/
def leavesConnectionReusable (config : Config) (method : Method) (head : Response.Head) : Bool :=
  config.enableKeepAlive
  ∧ H1.Message.Head.shouldKeepAlive (dir := .sending) head
  ∧ (responseBodySize method head).isSome

/--
The header and credentials to retry `request` with after `head` challenged it, or `none` when the
challenge goes to the caller unanswered: no authenticator is configured, the response is not a
challenge, the authenticator declined it, the request body cannot be replayed, or the exchange
leaves this connection unable to carry the retry.

The authenticator is consulted last, so a challenge that cannot be answered here never reaches
user code.
-/
private def challengeAnswer (connection : Connection) (request : Request Body.Any)
    (head : Response.Head) : Async (Option (Header.Name × Header.Value)) := do
  let some authenticator := connection.config.authenticator | return none
  let some kind := challengeKind? head.status | return none

  if request.body.reset?.isNone then return none
  if !leavesConnectionReusable connection.config request.line.method head then return none
  if ← connection.isClosed then return none

  let challenge : Challenge :=
    { kind, origin := connection.origin, target := request.line.uri, headers := head.headers }

  let some credential ← authenticator.authenticate challenge | return none
  return some (challenge.credentialHeader, credential)

/--
Reads the body of an intermediate response the client answers itself, keeping the bytes instead of
discarding them. Returns `none` once no whole body is left to hand back: more than `limit` bytes
arrived, so the body is abandoned and the stream closed and the rest left for the connection to
drain on its own, or the body failed partway through.

A failed body is reported as `none` rather than raised. The failure belongs to the exchange, which
states it as a typed `Error` on its completion promise; raising it from here would hand the caller
an untyped exception instead, which is the one thing `sendTracked` undertakes not to do.
-/
private partial def captureIntermediateBody (body : Body.Stream) (limit : Nat) :
    Async (Option ByteArray) := do
  let rec loop (captured : ByteArray) : Async (Option ByteArray) := do
    let received : Except IO.Error (Option Chunk) ←
      try .ok <$> body.recv catch e => pure (.error e)

    match received with
    | .error _ => return none
    | .ok none => return some captured
    | .ok (some chunk) =>
      let captured := captured ++ chunk.data

      if captured.size > limit then
        body.close
        return none

      loop captured

  loop .empty

/--
The challenge response as the peer sent it, rebuilt around the body `captureIntermediateBody` kept,
paired with the completion of an exchange that is already over.

Whether this connection can carry the authenticated retry is only knowable once the challenge
exchange has ended, and ending it means consuming the challenge's body. Holding on to those bytes is
what lets a challenge that turns out to be unanswerable still reach the caller whole, the way one
ruled out before its body was touched does.
-/
private def unansweredChallenge (response : Response Body.Stream) (captured : ByteArray) :
    Async TrackedResponse := do
  let body ← Body.mkStream
  Body.setKnownSize body (some (.fixed captured.size))

  background do
    unless captured.isEmpty do
      -- A caller that walks away closes the stream under the send; there is nothing to report.
      try body.send (Chunk.ofByteArray captured) catch _ => pure ()
    body.close

  let completion ← IO.Promise.new
  completion.resolve (.ok ())
  return { response := { response with body }, completion }

/--
Queues a request on the background loop and awaits its response head, together with the promise
that reports the end of the exchange. The request goes on the wire exactly as given.
-/
private def dispatch (connection : Connection) (request : Request Body.Any) (requestOverrides : RequestOverrides) :
    Async (Except Error TrackedResponse) := do
  let responsePromise ← IO.Promise.new
  let completionPromise ← IO.Promise.new

  let task ← connection.requestChannel.send
    { request, responsePromise, completionPromise, requestOverrides }

  let .ok _ ← await task
    | return .error (.closed "connection closed before request could be sent")

  return (← await responsePromise.result!).map ({ response := ·, completion := completionPromise })

/--
Runs one exchange on the connection: completes `request` against it, queues it, and hands the
response headers to the configured cookie handler. Returns the request as it went on the wire
alongside the outcome, since a challenge is answered against that form rather than the caller's.
-/
private def exchange (connection : Connection) (request : Request Body.Any) (requestOverrides : RequestOverrides) :
    Async (Request Body.Any × Except Error TrackedResponse) := do
  let sent ← connection.prepareRequest request
  let outcome ← connection.dispatch sent requestOverrides

  if let .ok tracked := outcome then
    connection.config.cookieHandler.forM
      (·.store connection.origin sent.line.uri tracked.response.line.headers)

  return (sent, outcome)

/--
Queues a request and awaits its response, together with a completion promise that
resolves when the connection is ready for the next request.
-/
def sendTracked (connection : Connection) (request : Request Body.Any) (requestOverrides : RequestOverrides := {}) :
    Async (Except Error TrackedResponse) := do
  let (sent, attempt) ← connection.exchange request requestOverrides

  let .ok ⟨response, completion⟩ := attempt | return attempt

  let some (name, credential) ← connection.challengeAnswer sent response.line
    | return attempt

  let captured ← captureIntermediateBody response.body
    connection.config.intermediateBodyDrainLimit

  let unanswered (err : Error) :=
    match captured with
    | some body => Except.ok <$> unansweredChallenge response body
    | none => pure (.error err)

  if let .error e ← await completion.result! then
    return (← unanswered e)

  if ← connection.isClosed then
    return (← unanswered (.closed "connection closed before the authenticated retry could be sent"))

  request.body.reset?.getD (pure ())

  let headers := (request.line.headers.erase name).insert name credential
  let retry := { request with line := { request.line with headers } }
  let (_, answered) ← connection.exchange retry requestOverrides

  if let .error e := answered then
    if e.isRetryable then
      return (← unanswered e)

  return answered

/--
Queues a request and awaits its response.
Use `sendTracked` to receive failures as a typed `Error` instead of a thrown exception.
-/
def send {β : Type} [Coe β Body.Any] (connection : Connection) (request : Request β)
    (requestOverrides : RequestOverrides := {}) : Async (Response Body.Stream) := do
  let sent ← connection.sendTracked { request with } requestOverrides
  return (← Error.throwOrPure sent).response

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
Retires the connection without disturbing the exchange running on it: no further request is
accepted, and the background loop shuts down once it next goes idle. `isClosed` reports `true`
immediately, so a pool stops handing this connection out right away.
-/
def retire (connection : Connection) : Async Unit :=
  stopAcceptingRequests connection.requestChannel

/--
Creates an HTTP client connection to `origin` over the given transport and starts its background
loop. The transport type `t` is used only during construction and is not stored in `Connection`.
-/
def new [Transport t] (client : t) (origin : URI.Origin) (config : Config := {}) : Async Connection := do
  let requestChannel ← Std.CloseableChannel.new
  let shutdown ← IO.Promise.new
  let context ← CancellationContext.new

  background do
    try
      run client { config := config.toH1Config } config context requestChannel
    finally
      shutdown.resolve ()

  let proxy := config.proxySelector.select origin
  pure { requestChannel, shutdown, config, context, origin, proxy }

end Std.Http.Client.Connection
