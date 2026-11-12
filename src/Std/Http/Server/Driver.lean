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
(`H1.Machine .receiving`) and decides everything a connection does: when to receive, what to write,
when to run the handler or ask it about `Expect: 100-continue`, how to hand the request body to the
handler and take the response body from it, which deadline runs, and when the connection ends.

A connection is its interpreter. It performs the `Command`s that `step` returns, waits on the sources
the state arms, and reports what happened as the next `Input`. The armed sources are read off the
state: a receive (`wantsBytes`), the request body's reader (`wantsBodyInterest`), the response body
(`pullsResponse`), the handler (`State.handlerRunning`), an `Expect: 100-continue` decision
(`State.asksContinue`), the writes (`State.watchesWrites`), the connection's cancellation
(`State.cancelled`) and the deadline (`nextDeadline`). An input from a source that is not armed is
ignored. After `Command.close` the interpreter stops.

The driver is total and keeps time only through its inputs: `step` gets the current time.
-/

namespace Std.Http.Server.Driver

set_option linter.all true

open Std Http Protocol Internal

/--
Limits and timeouts of the driver, in bytes and milliseconds.
-/
structure Config where
  /-- How many bytes to ask for in a receive when the machine does not say. -/
  recvSize : Nat := 8192
  /-- The most bytes to ask for in one receive. -/
  maxRecvSize : Nat := 8192
  /--
  While a response is under way, the connection reads ahead (for a pipelined request, or to see the
  peer close) only while it holds fewer unread bytes than this.
  -/
  readAhead : Nat := 8192
  /-- The response body is pulled only while at most this many written bytes are unconfirmed. -/
  writeLimit : Nat := 65536
  /-- How long an idle connection stays open, counted from when its writes completed. -/
  keepAliveTimeout : Nat := 12000
  /-- How long a request head may take to arrive, counted from its first byte. -/
  headerTimeout : Nat := 5000
  /--
  How long the connection waits for body bytes that a reader is waiting for, for the next chunk of a
  response body, and for a decision on `Expect: 100-continue`.
  -/
  lingeringTimeout : Nat := 10000
  /-- How long written bytes may stay unconfirmed. The connection is then dropped. -/
  writeTimeout : Nat := 30000
deriving Repr

/--
The driver configuration for a server configuration.
-/
def Config.ofServer (config : Http.Config) : Config where
  recvSize := config.defaultPayloadBytes
  maxRecvSize := config.maximumRecvSize
  readAhead := config.maximumRecvSize
  keepAliveTimeout := config.keepAliveTimeout.val.toInt.toNat
  headerTimeout := config.headerTimeout.toInt.toNat
  lingeringTimeout := config.lingeringTimeout.toInt.toNat
  writeTimeout := config.writeTimeout.toInt.toNat

/--
The deadlines a connection keeps. At most one of each kind runs at a time.
-/
inductive Deadline where
  /-- An idle connection closes without a response. -/
  | idle
  /-- A request head that started arriving has to be complete; answered with 408. -/
  | header
  /--
  Body bytes that a reader waits for, or the next chunk of the response body, have to arrive; answered
  with 408 when no response started, and otherwise by ending the connection.
  -/
  | linger
  /-- Written bytes have to be confirmed; the connection is dropped. -/
  | write
  /-- The handler has to decide on `Expect: 100-continue`; answered with 417. -/
  | «continue»
deriving BEq, DecidableEq, Repr, Inhabited

/--
What happened, reported by the interpreter.
-/
inductive Input where
  /-- Nothing happened: the driver only re-evaluates. Starts a connection. -/
  | resume
  /-- A receive returned bytes. -/
  | received (data : ByteArray)
  /-- A receive found the input over: the peer will send nothing more. -/
  | eof
  /-- A receive failed. -/
  | recvFailed (err : IO.Error)
  /-- Every write handed over so far completed. -/
  | written
  /-- A write failed. -/
  | writeFailed (err : IO.Error)
  /--
  The handler returned a response with head `head` and body length `size`, if known. `data` holds
  body chunks that were available at once, and `ended` says that the body ended after them.
  -/
  | responded (head : Response.Head) (size : Option Body.Length) (data : Array Chunk) (ended : Bool)
  /-- The handler failed. -/
  | handlerFailed (err : IO.Error)
  /-- A pull of the response body returned a chunk. -/
  | responseData (chunk : Chunk)
  /-- A pull of the response body found its end. -/
  | responseEnd
  /-- A pull of the response body failed. -/
  | responseFailed (err : IO.Error)
  /-- The handler decided on `Expect: 100-continue`. -/
  | continueDecided (accept : Bool)
  /-- The reader of the request body waits for data. -/
  | bodyWanted
  /-- The reader of the request body closed it. -/
  | bodyDropped
  /-- The deadline of the given kind passed. -/
  | deadline (kind : Deadline)
  /-- The connection's context was cancelled because the server shuts down. -/
  | shutdown
  /-- The connection's context was cancelled because its own deadline passed. -/
  | timedOut
  /-- An operation of the connection failed, and which one is not known. The connection ends. -/
  | failed (err : IO.Error)

/--
What the interpreter does, in order.
-/
inductive Command where
  /-- Write `data` after everything written before. Confirmed by `written` or `writeFailed`. -/
  | write (data : ChunkedBuffer)
  /--
  Create the request body, of length `size` if known and already closed when `complete`, and run the
  handler for `head`. Answered by `responded` or `handlerFailed`, unless abandoned.
  -/
  | startHandler (head : Request.Head) (size : Option Body.Length) (complete : Bool)
  /-- Ask the handler about `Expect: 100-continue`. Answered by `continueDecided`. -/
  | askContinue (head : Request.Head)
  /--
  Hand a chunk to the request body, whose reader waits, without waiting for it to be received. With
  `final`, the body ends after it.
  -/
  | pushBody (chunk : Chunk) (incomplete : Bool) (final : Bool)
  /-- Close the request body with `err`: the rest of it will not come. -/
  | failBody (err : IO.Error)
  /-- Close the response body, if one is held: nothing more is pulled from it. -/
  | releaseResponse
  /-- Report a failure to the handler (`Handler.onFailure`). -/
  | report (err : IO.Error)
  /-- The handler's response is no longer wanted: release it when it comes, instead of reporting it. -/
  | abandonHandler
  /--
  Close the transport, the last command. With `linger`, the peer may still be sending, so first shut
  down the write side and read until the peer closes its side (RFC 9112 §9.6): closing a socket with
  unread input resets the connection, which can destroy the response before the peer reads it.
  -/
  | close (linger : Bool)

/--
Where the connection is in its lifetime.
-/
inductive Phase where
  /-- Serving requests. -/
  | serving
  /-- Done; waiting for the writes in flight before closing. -/
  | draining
  /-- Closed. No input changes the state any more. -/
  | closed
deriving BEq, DecidableEq, Repr, Inhabited

/--
The request body handed to the handler of the current exchange.
-/
inductive BodyState where
  /-- No body is open: no handler started for this exchange, or the body ended or was closed. -/
  | closed
  /-- Open. With `wanted`, its reader waits for data that has not arrived. -/
  | «open» (wanted : Bool)
deriving BEq, DecidableEq, Repr, Inhabited

/--
The state of a connection. Everything about the exchange itself lives in the machine; this is what the
connection adds: the handler, the request body handed to it, the writes and the deadlines.
-/
structure State where
  /-- The protocol machine. -/
  machine : H1.Machine .receiving
  /-- Where the connection is in its lifetime. -/
  phase : Phase := .serving
  /-- A handler runs, and its response is wanted. -/
  handlerRunning : Bool := false
  /-- The request body. -/
  body : BodyState := .closed
  /-- Bytes written and not yet confirmed. -/
  unwritten : Nat := 0
  /-- The connection's context was cancelled: the connection answers no new request. -/
  cancelled : Bool := false
  /--
  What the connection waits for besides its writes, and until when: an idle connection, a request
  head, body bytes or a response chunk (`linger`), or an `Expect: 100-continue` decision. These never
  overlap.
  -/
  wait : Option (Deadline × Nat) := none
  /-- When the unconfirmed writes have to be confirmed. -/
  writeDeadline : Option Nat := none

namespace State

/--
The state of a new connection served by `machine`.
-/
def init (machine : H1.Machine .receiving) : State :=
  { machine }

/--
Sets the `Date` field value the machine writes into response heads.
-/
@[inline]
def setDate (s : State) (date : Option Header.Value) : State :=
  { s with machine := { s.machine with date } }

/--
Whether the interpreter has to report `Input.written`: written bytes are unconfirmed.
-/
@[inline]
def watchesWrites (s : State) : Bool :=
  s.unwritten > 0

/--
Whether an `Expect: 100-continue` decision was asked and is outstanding.
-/
@[inline]
def asksContinue (s : State) : Bool :=
  s.wait matches some (.«continue», _)

/--
Whether the connection is closed.
-/
@[inline]
def isClosed (s : State) : Bool :=
  s.phase == .closed

end State

/--
Whether the connection wants bytes from the peer: for a request head, for a body that its reader waits
for or that the machine drains, and, once the request was read and its response is under way, to read
ahead up to `readAhead` bytes. Never once the input is over.
-/
def wantsBytes (cfg : Config) (s : State) : Bool :=
  let m := s.machine
  s.phase == .serving && !m.reader.noMoreInput &&
    match m.reader.state with
    | .needStartLine | .needHeader _ => true
    | .readBody _ => !m.canPullBody || (s.body matches .open true)
    | .complete => m.writer.sentMessage && m.reader.remainingBytes < cfg.readAhead
    | _ => false

/--
How many bytes the receive that `wantsBytes` arms asks for.
-/
def recvSize (cfg : Config) (s : State) : Nat :=
  (s.machine.bodyBytesWanted.getD cfg.recvSize).min cfg.maxRecvSize

/--
Whether the connection watches the request body's reader, to learn when it waits for data or closes.
-/
@[inline]
def wantsBodyInterest (s : State) : Bool :=
  s.phase == .serving && (s.body matches .open false) && s.machine.canPullBody

/--
Whether the connection pulls the next chunk of the response body: the machine takes more of it, and
few written bytes are unconfirmed.
-/
@[inline]
def pullsResponse (cfg : Config) (s : State) : Bool :=
  s.phase == .serving && s.machine.writer.sentMessage && !s.machine.writer.noMoreUserData &&
    s.unwritten ≤ cfg.writeLimit

/--
The deadline the interpreter has to time: the earliest that runs. None once the connection closed.
-/
def nextDeadline (s : State) : Option (Deadline × Nat) :=
  if s.phase = .closed then none else
  match s.writeDeadline, s.wait with
  | some w, some (kind, t) => if t < w then some (kind, t) else some (.write, w)
  | some w, none => some (.write, w)
  | none, wait => wait

/--
Whether the deadline of kind `kind` runs and passed at `now`.
-/
private def due (s : State) (now : Nat) : Deadline → Bool
  | .write => s.writeDeadline.any (· ≤ now)
  | kind => s.wait.any fun (k, t) => k == kind && t ≤ now

/--
Why the request body stops before its end.
-/
private def bodyError (machine : H1.Machine .receiving) : IO.Error :=
  match machine.error with
  | some err => .userError s!"the request body is incomplete: {err}"
  | none =>
    if machine.writer.sentMessage then
      .userError "the request body was discarded after the response was written"
    else
      .userError "the connection closed before the request body was complete"

/--
Closes an open request body with an error: its end was not handed over, so it must not look
complete.
-/
@[inline]
private def failOpenBody (s : State) (cmds : Array Command) : State × Array Command :=
  match s.body with
  | .open _ => ({ s with body := .closed }, cmds.push (.failBody (bodyError s.machine)))
  | .closed => (s, cmds)

/--
Closes the connection at once, lingering only when `linger` is set and the peer may still send.
-/
@[inline]
private def closeNow (s : State) (linger : Bool) (cmds : Array Command) : State × Array Command :=
  ({ s with phase := .closed, unwritten := 0, writeDeadline := none },
    cmds.push (.close (linger && s.machine.peerMayStillSend)))

/--
Ends the connection: closes the request body, releases the response body and the handler's response,
then closes, after the writes in flight when `flush` is set. A connection that ends because a write
failed or timed out closes at once and does not linger.
-/
private def finish (cfg : Config) (s : State) (now : Nat) (flush : Bool) (cmds : Array Command) :
    State × Array Command :=
  let (s, cmds) := failOpenBody s cmds
  let cmds := cmds.push .releaseResponse
  let cmds := if s.handlerRunning then cmds.push .abandonHandler else cmds
  let s := { s with handlerRunning := false, wait := none }
  if flush && s.unwritten > 0 then
    ({ s with phase := .draining, writeDeadline := some (s.writeDeadline.getD (now + cfg.writeTimeout)) },
      cmds)
  else closeNow s flush cmds

/--
Applies an `Expect: 100-continue` decision, if one is asked. A rejected request is answered with 417
and its handler never runs.
-/
private def decideContinue (s : State) (accept : Bool) : Option (State × Array Command) :=
  if !s.asksContinue then none else
  let status := if accept then Status.«continue» else .expectationFailed
  some ({ s with wait := none, machine := s.machine.canContinue status }, #[])

/--
Gives the handler's response to the machine. A response that cannot be sent any more, because the
connection failed or closed meanwhile, is released. A 1xx status is interim, so it cannot end the
exchange (RFC 9110 §15.2): it is answered with 500 and reported.
-/
private def respond (s : State) (head : Response.Head) (size : Option Body.Length) (data : Array Chunk)
    (ended : Bool) : State × Array Command :=
  let s := { s with handlerRunning := false }
  if !s.machine.isWaitingMessage then (s, #[.releaseResponse]) else
  if head.status.isInformational then
    ({ s with machine := s.machine.closeWithError .internalServerError },
      #[.releaseResponse, .report (.userError
        s!"the handler returned the interim status {head.status.toCode} as its final response")])
  else
  let machine := match size with
    | some size => s.machine.setKnownSize size
    | none => s.machine
  let machine := machine.send head
  if machine.writer.omitBody then
    ({ s with machine }, #[.releaseResponse])
  else
    let machine := machine.sendData data
    if ended then ({ s with machine := machine.userClosedBody }, #[.releaseResponse])
    else ({ s with machine }, #[])

/--
Ends a request that took too long: answers 408 when no response started, and otherwise ends the
connection.
-/
private def timeOut (s : State) : State × Array Command :=
  ({ s with machine := s.machine.closeWithError .requestTimeout, wait := none },
    #[.report (.userError "request header timeout")])

/--
Answers a deadline that passed.
-/
private def fire (cfg : Config) (s : State) (now : Nat) : Deadline → Option (State × Array Command)
  | .idle => some (finish cfg s now true #[])
  | .header | .linger => some (timeOut s)
  | .write =>
    some (finish cfg { s with unwritten := 0, writeDeadline := none } now false
      #[.report (.userError s!"no write completed within {cfg.writeTimeout} ms")])
  | .«continue» => decideContinue s false

/--
Applies an input to a serving connection. An input from a source that is not armed, or a deadline
that does not run or has not passed, is ignored (`none`).
-/
private def apply (cfg : Config) (s : State) (now : Nat) : Input → Option (State × Array Command)
  | .resume => some (s, #[])
  | .received data =>
    if !wantsBytes cfg s then none else some ({ s with machine := s.machine.feed data }, #[])
  | .eof =>
    if !wantsBytes cfg s then none else some ({ s with machine := s.machine.noMoreInput }, #[])
  | .recvFailed err =>
    if !wantsBytes cfg s then none else some (finish cfg s now true #[.report err])
  | .written =>
    if s.unwritten == 0 then none else
    some ({ s with unwritten := 0, writeDeadline := none }, #[])
  | .writeFailed err =>
    some (finish cfg { s with unwritten := 0, writeDeadline := none } now false #[.report err])
  | .responded head size data ended =>
    if !s.handlerRunning then none else some (respond s head size data ended)
  | .handlerFailed err =>
    if !s.handlerRunning then none else
    some ({ s with handlerRunning := false, machine := s.machine.closeWithError .internalServerError },
      #[.report err])
  | .responseData chunk =>
    if !pullsResponse cfg s then none else some ({ s with machine := s.machine.sendData #[chunk] }, #[])
  | .responseEnd =>
    if !pullsResponse cfg s then none else
    some ({ s with machine := s.machine.userClosedBody }, #[.releaseResponse])
  | .responseFailed err =>
    if !pullsResponse cfg s then none else some (finish cfg s now true #[.report err])
  | .continueDecided accept => decideContinue s accept
  | .bodyWanted => if !wantsBodyInterest s then none else some ({ s with body := .open true }, #[])
  | .bodyDropped => if !wantsBodyInterest s then none else some ({ s with body := .closed }, #[])
  | .deadline kind => if due s now kind then fire cfg s now kind else none
  | .shutdown =>
    if s.cancelled then none else
    some ({ s with cancelled := true, machine := s.machine.closeWithError .serviceUnavailable }, #[])
  | .timedOut =>
    if s.cancelled then none else
    let (s, cmds) := timeOut s
    some ({ s with cancelled := true }, cmds)
  | .failed err => some (finish cfg s now true #[.report err])

/--
Hands the request body's waiting reader the next chunk, if the machine has one.
-/
private def deliverBody (s : State) (cmds : Array Command) : State × Array Command :=
  match s.body with
  | .open true =>
    match s.machine.pullBody with
    | (machine, none) => ({ s with machine }, cmds)
    | (machine, some pulled) =>
      -- An incomplete chunk is held by the body until the rest arrives, so its reader still waits.
      ({ s with machine, body := if pulled.final then .closed else .open pulled.incomplete },
        cmds.push (.pushBody pulled.chunk pulled.incomplete pulled.final))
  | _ => (s, cmds)

/--
Handles one event of the machine: a failure is reported, and an exchange that ended (`next`) closes
its request body and releases its response.
-/
private def processEvent (acc : State × Array Command) : H1.Event .receiving → State × Array Command
  | .failed err => (acc.1, acc.2.push (.report (.userError (toString err))))
  | .next =>
    let (s, cmds) := failOpenBody acc.1 acc.2
    (s, cmds.push .releaseResponse)
  | .endHeaders _ | .needMoreData _ | .«continue» | .closeBody | .needAnswer | .close => acc

/--
Steps the machine until it waits for something outside it, hands its output to the interpreter and
handles its events.
-/
private def runMachine (s : State) (cmds : Array Command) : State × Array Command :=
  let (machine, result) := s.machine.step
  let s := { s with machine }
  let (s, cmds) :=
    if result.output.size == 0 then (s, cmds)
    else ({ s with unwritten := s.unwritten + result.output.size }, cmds.push (.write result.output))
  result.events.foldl processEvent (s, cmds)

/--
Starts what the request waiting for an answer needs: the `Expect: 100-continue` decision, or else its
handler. Unconfirmed writes at this point belong to earlier responses, except the `100 Continue` sent
for this request. The decision, and the handler of a request with an unsafe method, wait for them,
since a write that fails ends the connection (RFC 9112 §9.3.2 lets a server process pipelined safe
requests in parallel).
-/
private def dispatch (cfg : Config) (s : State) (now : Nat) (cmds : Array Command) :
    State × Array Command :=
  let m := s.machine
  if s.handlerRunning || !m.isWaitingMessage then (s, cmds) else
  let head := m.reader.messageHead
  let earlierWrites := s.unwritten > 0
  if m.isReaderAwaitingContinue then
    if s.asksContinue || earlierWrites then (s, cmds) else
    ({ s with wait := some (.«continue», now + cfg.lingeringTimeout) }, cmds.push (.askContinue head))
  else if earlierWrites && !head.method.isSafe && !H1.expectsContinue head then (s, cmds)
  else
    let size := H1.Message.Head.getSize (dir := .receiving) head true
    let complete := size == some (.fixed 0)
    ({ s with handlerRunning := true, body := if complete then .closed else .open false },
      cmds.push (.startHandler head size complete))

/--
What the connection waits for besides its writes (`State.wait`): the `Expect: 100-continue` decision
it asked, the next response chunk, body bytes, a request head, or, once its writes are confirmed, the
next request on an idle connection.
-/
private def waitingFor (cfg : Config) (s : State) : Option Deadline :=
  if s.asksContinue then some .«continue»
  else if pullsResponse cfg s then some .linger
  else if !wantsBytes cfg s then none
  else match s.machine.reader.state with
    | .needStartLine =>
      if !s.machine.reader.input.atEnd then some .header
      else if s.unwritten == 0 then some .idle
      else none
    | .needHeader _ => some .header
    | .readBody _ => some .linger
    | _ => none

/--
How long a deadline of kind `kind` gives.
-/
private def Config.timeout (cfg : Config) : Deadline → Nat
  | .idle => cfg.keepAliveTimeout
  | .header => cfg.headerTimeout
  | .linger | .«continue» => cfg.lingeringTimeout
  | .write => cfg.writeTimeout

/--
Sets the deadlines that run in `s`. A deadline that keeps running keeps its time, except `linger`,
which every input restarts.
-/
private def rearm (cfg : Config) (s : State) (now : Nat) : State :=
  let wait := (waitingFor cfg s).map fun kind =>
    match s.wait with
    | some (k, t) => if k == kind && kind != .linger then (kind, t) else (kind, now + cfg.timeout kind)
    | none => (kind, now + cfg.timeout kind)
  { s with
    wait
    writeDeadline := if s.unwritten > 0 then some (s.writeDeadline.getD (now + cfg.writeTimeout)) else none }

/--
Advances a serving connection after an input: hands the request body's reader what arrived, steps
the machine, closes a request body the machine can no longer deliver, ends the connection once the
machine halted, and otherwise starts what is due and sets the deadlines.
-/
private def settle (cfg : Config) (s : State) (now : Nat) (cmds : Array Command) :
    State × Array Command :=
  let (s, cmds) := deliverBody s cmds
  let (s, cmds) := runMachine s cmds
  -- A body the machine can no longer deliver ends with an error, never as if complete.
  let (s, cmds) := if s.machine.canPullBody then (s, cmds) else failOpenBody s cmds
  if s.machine.halted then finish cfg s now true cmds else
  let (s, cmds) := dispatch cfg s now cmds
  (rearm cfg s now, cmds)

/--
Answers an input at time `now` (monotonic milliseconds): returns the new state and the commands to
perform, in order.
-/
def step (cfg : Config) (s : State) (now : Nat) (input : Input) : State × Array Command :=
  match s.phase with
  | .closed => (s, #[])
  | .draining =>
    match input with
    | .written => closeNow s true #[]
    | .writeFailed err => closeNow s false #[.report err]
    | .deadline .write =>
      if due s now .write then
        closeNow s false #[.report (.userError s!"no write completed within {cfg.writeTimeout} ms")]
      else (s, #[])
    | _ => (s, #[])
  | .serving =>
    match apply cfg s now input with
    | none => (s, #[])
    | some (s, cmds) => if s.phase == .serving then settle cfg s now cmds else (s, cmds)

/--
Starts a connection served by `machine` at time `now`.
-/
def start (cfg : Config) (machine : H1.Machine .receiving) (now : Nat) : State × Array Command :=
  step cfg (State.init machine) now .resume

theorem step_closed (cfg : Config) (s : State) (now : Nat) (input : Input) (h : s.phase = .closed) :
    step cfg s now input = (s, #[]) := by
  simp [step, h]

/-- Bytes from a receive that is not armed change nothing. -/
theorem step_received_unarmed (cfg : Config) (s : State) (now : Nat) (data : ByteArray)
    (h : s.phase = .serving) (hr : wantsBytes cfg s = false) :
    step cfg s now (.received data) = (s, #[]) := by
  simp [step, apply, h, hr]

/-- An end of input from a receive that is not armed changes nothing. -/
theorem step_eof_unarmed (cfg : Config) (s : State) (now : Nat)
    (h : s.phase = .serving) (hr : wantsBytes cfg s = false) :
    step cfg s now .eof = (s, #[]) := by
  simp [step, apply, h, hr]

/-- A cancellation is answered once. -/
theorem step_shutdown_twice (cfg : Config) (s : State) (now : Nat)
    (h : s.phase = .serving) (hs : s.cancelled = true) :
    step cfg s now .shutdown = (s, #[]) := by
  simp [step, apply, h, hs]

theorem nextDeadline_closed (s : State) (h : s.phase = .closed) : nextDeadline s = none := by
  simp [nextDeadline, h]

end Std.Http.Server.Driver
