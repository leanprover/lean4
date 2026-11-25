/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Protocol.H1
public import Std.Http.Server.Config

public section

/-!
# Connection driver

The decisions of an HTTP/1.1 server connection, without I/O. The driver wraps the protocol machine
(`H1.Machine .receiving`) and decides everything else a connection does: which timeout runs, what
it waits on, when the handler runs or is asked about `Expect: 100-continue`, how the request body
reaches the handler and the response body reaches the machine, how a request is aborted, and how
the connection ends.

A connection is the driver's interpreter. It performs the `Command`s that `step` returns, in order,
and reports what happened as the next `Input`:
- After a batch with a write command (`write`, `awaitWritten`, `flush`), always its last, the next
  input is `written`, with whether the writes succeeded. A write that fails ends its batch.
- Otherwise, while `State.waits` holds, the interpreter waits: on the `Expect: 100-continue`
  decision when `State.asksContinue`, and otherwise on the `sources` of the state, under the `Arm`
  they give, which cancels the connection's context when the wait outlives it.
- Otherwise the next input is `resume`.

After `close`, the interpreter stops. The driver keeps time only through `step`'s arguments.
-/

namespace Std.Http.Server.Driver

set_option linter.all true

open Std Http Protocol Internal Time

/-! ## Interface -/

/--
The timeout that applies while the connection waits on its peer.
-/
inductive Timer where
  /--
  The connection is idle between requests, and closes quietly once the keep-alive timeout passes
  after its last write completes.
  -/
  | keepAlive
  /-- A request head is being read, and must be complete by `deadline`, a value of `IO.monoMsNow`. -/
  | header (deadline : Nat)
  /-- A request head was read, and the connection fails when a wait takes longer than `timeout`. -/
  | request (timeout : Millisecond.Offset)

/--
What happened, reported by the interpreter.
-/
inductive Input where
  /-- Nothing happened. Starts a connection. -/
  | resume
  /-- The socket returned bytes, or `none` once the peer closed its side. -/
  | received (data : Option ByteArray)
  /-- The writes of the last batch succeeded, or one failed. -/
  | written (ok : Bool)
  /--
  The handler returned a response with head `head`, whose body has length `size` if known. For a
  response the driver writes the body of (`writesBody`), `first` is one non-blocking receive from
  the body, or its failure; otherwise it is `.ok none`. A body that ended at once is closed already.
  -/
  | responded (head : Response.Head) (size : Option Body.Length)
      (first : Except IO.Error (Option (Option Chunk)))
  /-- The handler failed. -/
  | handlerFailed (err : IO.Error)
  /-- The response body returned a chunk, or `none` at its end. -/
  | pulled (chunk : Option Chunk)
  /-- The request body's reader waits for data, or the body ended. -/
  | bodyInterest (wanted : Bool)
  /-- The handler decided on `Expect: 100-continue`, or the wait for it ended (`false`). -/
  | continueDecided (accept : Bool)
  /--
  The connection's context was cancelled: by the timer of the sources (`byTimer`), by the context's
  own deadline (`deadline`), or else because the server shuts down.
  -/
  | cancelled (byTimer : Bool) (deadline : Bool)
  /-- A wait failed, and the interpreter reported it. -/
  | failed

/--
What the interpreter does, in order.
-/
inductive Command where
  /-- Hand `data` to the writes, possibly empty, which fails once a write failed. -/
  | write (data : ChunkedBuffer)
  /-- Wait until every write handed over completed. -/
  | awaitWritten
  /-- Wait until the writes in flight complete, before closing. -/
  | flush
  /-- Run the handler for `head`, with the request body. -/
  | startHandler (head : Request.Head)
  /-- Ask the handler whether to accept `Expect: 100-continue` for `head`. -/
  | askContinue (head : Request.Head)
  /-- Set the request body's length. -/
  | setBodySize (size : Body.Length)
  /--
  Offer `chunk` to the request body without waiting for it to be taken, since its reader may have
  withdrawn. With `final`, the body ends after it.
  -/
  | offerBody (chunk : Chunk) (incomplete : Bool) (final : Bool)
  /--
  End the request body: cleanly when all its bytes were delivered, and otherwise with an error
  saying `reason`, so a truncated body never looks complete.
  -/
  | endBody (reason : String)
  /--
  Start the next exchange: a new request body and a new place for the handler's response, so the
  response of a handler still running is not waited for.
  -/
  | nextExchange
  /-- Close the response body, if one is held. -/
  | closeResponse
  /-- Close the response body of a handler still running once it returns, since it is not written. -/
  | releaseHandler
  /-- Report a failure to the handler (`Handler.onFailure`). -/
  | report (err : IO.Error)
  /--
  End the connection, after reading and discarding input until the peer closes its side or the
  lingering timeout passes when `linger` is set (RFC 9112 §9.6): closing a socket the client still
  sends on resets the connection, which can destroy the response before the client reads it.
  -/
  | close (linger : Bool)

/--
What the driver waits for.
-/
inductive Stage where
  /-- The next input is `resume`, and steps the machine. -/
  | running
  /-- The machine's output of this pass was handed over; its `events` follow once it is `written`. -/
  | writing (events : List (H1.Event .receiving))
  /-- The `Expect: 100-continue` decision, after which the `events` left of this pass follow. -/
  | asking (events : List (H1.Event .receiving))
  /-- An input from the sources. -/
  | polling
  /-- The writes in flight, before closing. -/
  | flushing
  /-- Nothing: the connection is closed. -/
  | closed

/--
The state of a connection. The exchange itself lives in the machine; this is what the connection
adds.
-/
structure State where
  /-- The protocol machine. -/
  machine : H1.Machine .receiving
  /-- What the driver waits for. -/
  stage : Stage := .running
  /-- The timeout that applies while the connection waits on its peer. -/
  timer : Timer := .keepAlive
  /-- Set when the machine asked for more input in the last step, with the bytes it expects if known. -/
  inputWanted : Option (Option Nat) := none
  /--
  A handler runs and its response is waited for. A handler still running after its exchange ended,
  as after a timeout, does not count: its response is not written.
  -/
  handlerRunning : Bool := false
  /-- A response body is being written, and the connection holds it. -/
  responseBody : Bool := false
  /-- A request head waits for its handler. -/
  pendingHead : Option Request.Head := none
  /-- The current request was read to its end, or none has started. -/
  requestEnded : Bool := true
  /-- The second, since the Unix epoch, that the machine's `Date` was formatted for. -/
  dateSecond : Option Int := none

namespace State

/--
Whether the interpreter waits for the next input: on the `Expect: 100-continue` decision, or on the
sources.
-/
def waits (s : State) : Bool :=
  s.stage matches .polling | .asking _

/--
Whether the interpreter waits for the `Expect: 100-continue` decision.
-/
def asksContinue (s : State) : Bool :=
  s.stage matches .asking _

/--
Whether the connection is closed.
-/
def isClosed (s : State) : Bool :=
  s.stage matches .closed

/--
Whether `sources` needs to know if the request body is open and its reader waits.
-/
def readsBodyState (s : State) : Bool :=
  s.machine.canPullBody

end State

/--
The state of a new connection served by `machine`.
-/
def init (machine : H1.Machine .receiving) : State :=
  { machine }

/-! ## What the interpreter waits on -/

/--
When a request head starting at `now` must be complete.
-/
private def headerDeadline (cfg : Http.Config) (now : Nat) : Timer :=
  .header (now + cfg.headerTimeout.toInt.toNat)

/--
How the interpreter times a wait: the connection's context is cancelled when it outlives this.
-/
inductive Arm where
  /-- The wait must end by `deadline`, a value of `IO.monoMsNow`. -/
  | until (deadline : Nat)
  /-- The wait must end within `timeout`. -/
  | within (timeout : Millisecond.Offset)
  /--
  The wait must end within `timeout` of the writes in flight completing, or of now if none are: a
  peer may still be reading the response, so an idle connection's timeout starts once it is written.
  -/
  | afterWrites (timeout : Millisecond.Offset)

/--
What the interpreter waits on, besides the connection's context.
-/
structure Sources where
  /-- Receive from the socket, at most this many bytes. -/
  recv : Option Nat
  /-- How the wait is timed. -/
  timer : Option Arm
  /-- The handler's response. -/
  response : Bool
  /-- The response body. -/
  responseBody : Bool
  /-- The request body's reader, to learn when it waits for data or the body ends. -/
  requestBody : Bool

/--
What the interpreter waits on while polling, given whether the request body is open (`bodyOpen`) and
its reader waits (`bodyInterested`), both read only when `State.readsBodyState`.

Once `maximumRecvSize` bytes of input wait unread and the machine needs no more to make progress,
the socket is left out, so the rest waits in the kernel and pushes back on the client, for example
while a response streams.
-/
def sources (cfg : Http.Config) (s : State) (bodyOpen bodyInterested : Bool) : Sources :=
  let m := s.machine
  let requestBodyOpen := m.canPullBody && bodyOpen
  let requestBodyInterested := requestBodyOpen && bodyInterested

  -- A pull that found too few bytes waits for input even once its reader is gone, as when another
  -- case won the reader's select. The reader stays out until input arrives, so without the socket
  -- nothing would wake the loop when it asks again.
  let pullStalled := requestBodyOpen && !m.canPullBodyNow

  -- The socket is polled only when there is more to do than waiting for the handler alone.
  let pollSocket :=
    !s.handlerRunning || s.responseBody || m.writer.sentMessage || requestBodyInterested || pullStalled

  let inputFull := m.reader.remainingBytes ≥ cfg.maximumRecvSize && s.inputWanted.isNone

  -- The request timer times a wait on the client: for more of the request, or for a body chunk a
  -- reader asked for. A wait on the handler alone is not timed, since a response may pause as long
  -- as the handler wants (server-sent events, long polling); a peer that stops reading is bounded
  -- by `writeTimeout`.
  let waitsOnPeer := s.inputWanted.isSome || pullStalled || requestBodyInterested
  let timer : Option Arm :=
    match s.timer with
    | .keepAlive => some (.afterWrites cfg.keepAliveTimeout.val)
    | .header deadline => some (.until deadline)
    | .request timeout => if waitsOnPeer then some (.within timeout) else none

  {
    -- After EOF the socket stays readable, returning `none` at once, so polling it would spin.
    recv :=
      if pollSocket && !m.reader.noMoreInput && !inputFull then
        some ((s.inputWanted.join.getD cfg.defaultPayloadBytes).min cfg.maximumRecvSize)
      else none
    timer := if pollSocket then timer else none
    response := s.handlerRunning
    responseBody := s.responseBody
    requestBody := requestBodyOpen && m.canPullBodyNow
  }

/--
Whether the body of the handler's response with `head` and `size` is written. It is not when the
machine no longer waits for a response, as after a failure, or omits the body, as for a `HEAD`
request, a 204 or 304 response, or a response the machine rejects.
-/
def writesBody (s : State) (head : Response.Head) (size : Option Body.Length) : Bool :=
  s.machine.isWaitingMessage && !(s.machine.sendResponse head size).writer.omitBody

/--
Whether the connection ends while the client may still be sending: the client has not closed its
side, and the machine stopped before the end of a request, or, while it still took input, with input
it never read, or at the end of an exchange. A request rejected from its head alone leaves
`requestEnded` set, so only `machine.failed` shows it. The loop does not read while a handler runs,
so requests the client pipelined meanwhile wait unread in the transport (RFC 9112 §9.3.2), whether
or not the request asked to keep the connection open.
-/
def peerMayStillSend (s : State) : Bool :=
  let reader := s.machine.reader
  let unreadInput :=
    s.machine.failed || reader.remainingBytes > 0 || (reader.state matches .readBody _)
  !reader.peerClosed &&
    (!s.requestEnded || (!reader.inputStopped && unreadInput) || (s.timer matches .request _))

/-! ## Passes of the machine -/

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
Ends the connection: ends the request body and the response, then waits for the writes in flight.
-/
private def finish (s : State) (cmds : Array Command) : State × Array Command :=
  ({ s with stage := .flushing },
    cmds ++ #[.endBody "the connection closed before the request body was complete", .closeResponse,
      .releaseHandler, .flush])

/--
Ends the exchange with `status`. The response body in progress can no longer be sent, so it is
closed, and the connection stops waiting on it.
-/
private def abortWith (s : State) (status : Status) (cmds : Array Command) : State × Array Command :=
  ({ s with
      machine := s.machine.closeWithError status, handlerRunning := false, responseBody := false },
    if s.responseBody then cmds.push .closeResponse else cmds)

/--
Dispatches a request head waiting for its handler, and decides whether the next input comes from the
sources or the next pass of the machine.
-/
private def endPass (s : State) (cmds : Array Command) : State × Array Command :=
  let (s, cmds) :=
    match s.pendingHead with
    | some head => ({ s with pendingHead := none, handlerRunning := true }, cmds.push (.startHandler head))
    | none => (s, cmds)
  let polls := s.inputWanted.isSome || s.handlerRunning || s.responseBody || s.machine.canPullBody
  ({ s with stage := if polls then .polling else .running }, cmds)

/--
Processes the events of one pass of the machine, then ends the pass. An `Expect: 100-continue`
decision suspends the pass until it is made; a failure skips the events after it.
-/
private def processEvents (cfg : Http.Config) (now : Nat) (s : State) (cmds : Array Command) :
    List (H1.Event .receiving) → State × Array Command
  | [] => endPass s cmds
  | event :: rest =>
    match event with
    | .needMoreData expect => processEvents cfg now { s with inputWanted := some expect } cmds rest
    | .needAnswer | .close => processEvents cfg now s cmds rest
    | .endHeaders head =>
      let s := { s with
        timer := .request cfg.lingeringTimeout, pendingHead := some head, requestEnded := false }
      let cmds := match head.getSize true with
        | some length => cmds.push (.setBodySize length)
        | none => cmds
      processEvents cfg now s cmds rest
    | .«continue» =>
      match s.pendingHead with
      | some head => ({ s with stage := .asking rest }, cmds.push (.askContinue head))
      | none => processEvents cfg now s cmds rest
    | .next =>
      -- Input already buffered is the start of the next request, so its head is due by the header
      -- deadline; only an empty connection waits under the keep-alive timeout.
      let timer :=
        if s.machine.reader.remainingBytes > 0 then headerDeadline cfg now else .keepAlive
      let cmds := cmds ++ #[.endBody "the request body was discarded after the response was written",
        .closeResponse, .nextExchange]
      processEvents cfg now
        { s with responseBody := false, timer, handlerRunning := false } cmds rest
    | .failed err =>
      let cmds := cmds ++ #[.report (.userError (toString err)),
        .endBody s!"the request body is incomplete: {err}"]
      endPass { s with inputWanted := none, pendingHead := none } cmds
    | .closeBody =>
      -- A body read to its end was closed with its final chunk, so an open body here means the rest
      -- of it was drained after the response was written.
      let cmds := cmds.push (.endBody "the request body was discarded after the response was written")
      processEvents cfg now { s with requestEnded := true } cmds rest

/--
Runs one pass of the machine and hands its output to the writes, waiting for the earlier writes too
when an event needs them.
-/
private def pass (s : State) : State × Array Command :=
  if s.machine.halted then
    finish s #[]
  else
    let (machine, result) := s.machine.step
    let cmds := #[.write result.output]
    let cmds := if result.events.any needsWrittenOutput then cmds.push .awaitWritten else cmds
    ({ s with machine, stage := .writing result.events.toList }, cmds)

/-! ## Inputs -/

/--
Answers a request whose wait outlived its timer, or whose context's deadline passed, with 408.
-/
private def timeOut (s : State) : State × Array Command :=
  let what := if s.timer matches .header _ then "request header timeout" else "request timeout"
  abortWith s .requestTimeout #[.report (.userError what)]

/--
Applies the handler's response.
-/
private def respond (s : State) (head : Response.Head) (size : Option Body.Length)
    (first : Except IO.Error (Option (Option Chunk))) : State × Array Command :=
  let writes := writesBody s head size
  let machine := s.machine.sendResponse head size
  let s := { s with machine, handlerRunning := false }
  if !writes then
    (s, #[.closeResponse])
  else
    match first with
    | .ok none => ({ s with responseBody := true }, #[])
    | .ok (some (some chunk)) => ({ s with machine := machine.sendData #[chunk], responseBody := true }, #[])
    | .ok (some none) => ({ s with machine := machine.userClosedBody }, #[.closeResponse])
    | .error err => finish { s with responseBody := true } #[.report err]

/--
Applies an input from the sources. Unless it ends the connection, the next pass of the machine
follows.
-/
private def apply (cfg : Http.Config) (s : State) (now : Nat) : Input → State × Array Command
  | .received (some data) =>
    -- The first byte after idle starts the request head, which the header timeout bounds.
    let timer := if s.timer matches .keepAlive then headerDeadline cfg now else s.timer
    ({ s with timer, machine := s.machine.feed data }, #[])
  | .received none => ({ s with machine := s.machine.noMoreInput }, #[])
  | .pulled (some chunk) => ({ s with machine := s.machine.sendData #[chunk] }, #[])
  | .pulled none => ({ s with machine := s.machine.userClosedBody, responseBody := false }, #[.closeResponse])
  | .bodyInterest true =>
    match s.machine.pullBody with
    | (machine, some pulled) =>
      ({ s with machine }, #[.offerBody pulled.chunk pulled.incomplete pulled.final])
    | (machine, none) => ({ s with machine }, #[])
  | .cancelled byTimer deadline =>
    if byTimer then
      if s.timer matches .keepAlive then finish s #[] else timeOut s
    else if deadline then timeOut s
    else abortWith s .serviceUnavailable #[]
  | .handlerFailed err => abortWith s .internalServerError #[.report err]
  | .responded head size first => respond s head size first
  | .failed => finish s #[]
  | .resume | .bodyInterest false | .written _ | .continueDecided _ => (s, #[])

/-! ## Stepping -/

/--
Keeps the machine's `Date` current at wall-clock time `wall` when `Config.generateDate` is set,
formatting it at most once per second.
-/
private def refreshDate (cfg : Http.Config) (s : State) (wall : Option Timestamp) : State :=
  match wall with
  | some wall =>
    let second := wall.toSecondsSinceUnixEpoch.val
    if !cfg.generateDate || s.dateSecond == some second then s
    else
      let date := Header.Value.ofString! (DateTime.ofTimestamp wall TimeZone.ZoneRules.UTC).toHTTPDateString
      { s with machine := { s.machine with date := some date }, dateSecond := some second }
  | none => s

/--
Answers an input at time `now` (`IO.monoMsNow`), and wall-clock time `wall` for the `Date` header:
returns the new state and the commands to perform, in order.
-/
def step (cfg : Http.Config) (s : State) (now : Nat) (input : Input) (wall : Option Timestamp := none) :
    State × Array Command :=
  let s := refreshDate cfg s wall
  match s.stage, input with
  | .closed, _ => (s, #[])
  | .flushing, .written ok => ({ s with stage := .closed }, #[.close (ok && peerMayStillSend s)])
  | .flushing, _ => (s, #[])
  | .writing events, .written ok =>
    if ok then processEvents cfg now s #[] events else finish s #[]
  | .writing _, _ => (s, #[])
  | .asking events, .continueDecided accept =>
    let status := if accept then Status.«continue» else .expectationFailed
    let s := { s with machine := s.machine.canContinue status }
    processEvents cfg now (if accept then s else { s with pendingHead := none }) #[] events
  | .asking _, _ => (s, #[])
  | .polling, input =>
    let (s, cmds) := apply cfg { s with inputWanted := none } now input
    if s.stage matches .flushing then (s, cmds)
    else
      let (s, more) := pass s
      (s, cmds ++ more)
  | .running, _ => pass s

/--
A closed connection ignores every input.
-/
theorem step_closed (cfg : Http.Config) (s : State) (now : Nat) (input : Input)
    (h : s.stage = .closed) : step cfg s now input = (s, #[]) := by
  simp [step, refreshDate, h]

end Std.Http.Server.Driver
