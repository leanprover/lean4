/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Protocol.H1
public import Std.Http.Client.Config
public import Std.Http.Client.Error
public import Std.Http.Client.Authenticator

public section

/-!
# Connection driver

The decisions of an HTTP/1.1 client connection, without I/O. The driver wraps the protocol machine
(`H1.Machine .sending`) and decides everything else a connection does for the exchanges it carries
one after another: when the request body is pulled and when it is abandoned, how the response head
and body reach the caller, which timeout runs, and how an exchange and the connection end.

A connection is the driver's interpreter. It performs the `Command`s that `step` returns, in order,
and reports what happened as the next `Input`:
- After a batch with a write command (`write`, `awaitWritten`, `flush`), always its last, the next
  input is `written`, with whether the writes succeeded and where the writes handed over stand.
  `write` only hands the data over, so the connection goes on reading while an upload is blocked and
  sees a response that answers it early.
- Otherwise, while `State.waits` holds, the interpreter waits on the `sources` of the state.
- Otherwise the next input is `resume`.

After `close`, the interpreter stops. The driver keeps time only through `step`'s arguments, in
milliseconds of a monotonic clock.
-/

namespace Std.Http.Client.Connection.Driver

set_option linter.all true

open Std Http Protocol Internal

/-! ## Interface -/

/--
A timeout the interpreter arms while it waits.
-/
inductive Timer where
  /-- No exchange runs, and the connection closes quietly once `keepAliveTimeout` passes. -/
  | idle
  /-- An exchange waits on bytes from the peer for longer than `readTimeout`. -/
  | read
  /-- An exchange made no progress for `requestTimeout`. -/
  | request
  /-- A request with `Expect: 100-continue` waited `expectContinueTimeout` for the interim response. -/
  | «continue»
deriving Repr, BEq

/--
How a timer is armed.
-/
inductive Arm where
  /-- It fires at `deadline`, in milliseconds of the clock `step` is given. -/
  | until (deadline : Nat)
  /-- It fires `timeout` milliseconds after the wait starts. -/
  | within (timeout : Nat)
deriving Repr, BEq

/--
Where the writes handed over stand, as the interpreter reports them after a batch.
-/
inductive Writes where
  /-- Every write completed. -/
  | idle
  /-- A write is in flight: the wait is on the peer taking the bytes. -/
  | inFlight
  /-- More is queued behind the write in flight than the connection lets wait. -/
  | backlogged
deriving Repr, BEq

/--
What happened, reported by the interpreter.
-/
inductive Input where
  /-- Nothing happened. Starts a connection. -/
  | resume
  /--
  A caller sent a request with head `head`, a body of length `size` when known, and `overrides` on
  the connection's configuration. Reported while `Sources.request` holds; otherwise it is refused.
  -/
  | submit (head : Request.Head) (size : Option Body.Length) (overrides : RequestOverrides)
  /-- The socket returned bytes, or `none` once the peer closed its side. -/
  | received (data : Option ByteArray)
  /-- The writes of the last batch succeeded, or one failed, and where the writes stand. -/
  | written (ok : Bool) (writes : Writes)
  /-- The writes handed over all completed, after `Sources.writesIdle` asked to know. -/
  | writesIdle
  /-- The request body returned a chunk, or `none` at its end. -/
  | pulled (chunk : Option Chunk)
  /-- The request body failed. -/
  | pullFailed (err : IO.Error)
  /-- The caller waits for more of the response body (`true`), or closed it (`false`). -/
  | bodyInterest (wanted : Bool)
  /-- A timer of the sources fired. -/
  | fired (timer : Timer)
  /-- The connection was shut down. -/
  | cancelled
  /-- Reading from the socket failed. -/
  | failed (err : IO.Error)

/--
What the interpreter does, in order.
-/
inductive Command where
  /-- Hand `data` to the writes, possibly empty, without waiting for them. -/
  | write (data : ChunkedBuffer)
  /-- Wait until every write handed over completed. -/
  | awaitWritten
  /-- Wait until the writes in flight complete, before closing. -/
  | flush
  /-- An informational (`1xx`) response arrived. -/
  | interim (head : Response.Head)
  /-- The response body ended with these trailer fields; it comes before the body's end. -/
  | trailers (fields : Headers)
  /-- Give the caller the response head, with the length of its body when known. -/
  | deliverHead (head : Response.Head) (size : Option Body.Length)
  /-- Offer `chunk` to the response body, which ends after it with `final`. -/
  | offerBody (chunk : Chunk) (final : Bool)
  /--
  Close the response body before the exchange ends: the caller has all of it, but the exchange
  waits for a request body that may take long.
  -/
  | endResponse
  /-- Close the request body: it was sent, or it is not wanted anymore. -/
  | closeRequestBody
  /--
  End the exchange successfully: report it complete, and close the response body if it is still
  held and the request body.
  -/
  | complete
  /-- End the exchange with `err`, and fail its response body if it is still open. -/
  | reject (err : Client.Error)
  /-- Fail the request just submitted with `err`: it never started. -/
  | refuse (err : Client.Error)
  /-- Stop accepting requests: this connection carries no further exchange. -/
  | stopAccepting
  /-- End the connection. -/
  | close

/-- The request body of the exchange. -/
inductive Upload where
  /-- Held back until the server answers `Expect: 100-continue`. -/
  | parked
  /-- Pulled from the caller and handed to the machine. -/
  | open
  /-- Sent, abandoned, or never there. -/
  | done
deriving Repr, BEq

/-- The response body of the exchange, as the caller holds it. -/
inductive Download where
  /-- No final response head yet. -/
  | waiting
  /-- The caller reads it. -/
  | open
  /-- The caller closed it before its end, so the machine drains the rest. -/
  | abandoned
  /-- The caller has all of it, and the stream stays open until the exchange ends. -/
  | held
  /-- Closed. -/
  | done
deriving Repr, BEq

/--
The state of one exchange.
-/
structure Exchange where
  /-- The method of the request, which decides whether its response has content. -/
  method : Method
  /-- The configuration of this exchange: the connection's, with the request's overrides. -/
  config : Client.Config
  /-- The request body. -/
  upload : Upload
  /-- The response body. -/
  download : Download := .waiting
  /-- When the exchange fails unless it makes progress before. -/
  deadline : Nat
  /-- When a parked request body is sent without the interim response. -/
  continueDeadline : Option Nat := none
  /-- The interim (`1xx`) responses received. -/
  interim : Nat := 0
  /-- Any of the request was handed to the writes. -/
  headSent : Bool := false
  /-- The final response head reached the caller. -/
  finalHead : Bool := false
  /-- The whole response body reached the caller. -/
  responseComplete : Bool := false

/--
What the driver waits for.
-/
inductive Stage where
  /-- The next input is `resume`, and steps the machine. -/
  | running
  /--
  The machine's output was handed over; its `events` follow once it is `written`. With `awaited`,
  the batch waited for every write, as the event ending an exchange needs.
  -/
  | writing (events : List (H1.Event .sending)) (awaited : Bool := false)
  /-- An input from the sources. -/
  | polling
  /-- The writes in flight, before closing. -/
  | flushing
  /-- Nothing: the connection is closed. -/
  | closed

/--
The state of a connection. The protocol lives in the machine; this is what the connection adds.
-/
structure State where
  /-- The protocol machine. -/
  machine : H1.Machine .sending
  /-- What the driver waits for. -/
  stage : Stage := .running
  /-- The exchange in flight. -/
  exchange : Option Exchange := none
  /-- Set when the machine asked for more input in the last step, with the bytes it expects. -/
  inputWanted : Option (Option Nat) := none
  /-- The connection takes further requests. -/
  accepting : Bool := true
  /-- Where the writes handed over stand, as last reported. -/
  writes : Writes := .idle

namespace State

/-- Whether the interpreter waits on the sources for the next input. -/
def waits (s : State) : Bool :=
  s.stage matches .polling

/-- Whether the connection is closed. -/
def isClosed (s : State) : Bool :=
  s.stage matches .closed

/-- Whether no exchange runs and the connection takes the next request. -/
def idle (s : State) : Bool :=
  s.exchange.isNone && s.accepting && !s.isClosed

end State

/--
The state of a new connection over `machine`.
-/
def init (machine : H1.Machine .sending) : State :=
  { machine }

@[inline] private def millis (timeout : Client.Timeout) : Nat :=
  timeout.val.toInt.toNat

/-! ## What the interpreter waits on -/

/--
What the interpreter waits on, besides the connection's shutdown.
-/
structure Sources where
  /-- Receive from the socket, at most this many bytes. -/
  recv : Option Nat
  /-- The next request from a caller. -/
  request : Bool
  /-- The next chunk of the request body. -/
  requestBody : Bool
  /-- The writes handed over completing, to resume pulling the request body. -/
  writesIdle : Bool
  /--
  A write stalling: no write completing for the connection's write timeout, which then ends the
  exchange as `fired .request` does. It stands in for the request timer while writes are in flight,
  since each write that completes is progress.
  -/
  writesLate : Bool
  /-- The caller waiting for more of the response body, or closing it. -/
  responseInterest : Bool
  /-- Only the caller closing the response body: there is nothing to hand over yet. -/
  responseClosed : Bool
  /-- The timers to arm. -/
  timers : Array (Timer × Arm)

/--
What the interpreter waits on while polling. While writes are in flight the wait is on the peer
taking them, so `readTimeout` does not run and `writesIdle` reports when they complete; while they
are backlogged the request body is not pulled further either.

While the caller holds response body bytes it has not taken, the socket is left out once
`maximumRecvSize` bytes of input wait unread, so the rest waits in the kernel and pushes back on the
peer.
-/
def sources (cfg : Client.Config) (s : State) : Sources :=
  let m := s.machine
  let backlogged := s.writes == .backlogged
  match s.exchange with
  | none =>
    { recv := if m.needsInput then some (cfg.defaultPayloadBytes.min cfg.maximumRecvSize) else none
      request := s.accepting
      requestBody := false
      writesIdle := false
      writesLate := false
      responseInterest := false
      responseClosed := false
      timers := #[(.idle, .within (millis cfg.keepAliveTimeout))] }
  | some ex =>
    let cfg := ex.config
    let pullable := m.canPullBodyNow && ex.download == .open
    let awaitsCaller := (pullable && m.hasBufferedInput) || ex.upload == .open
    let inputFull := pullable && m.hasBufferedInput && m.bufferedInputBytes ≥ 4 * cfg.maximumRecvSize
    let recv :=
      if m.needsInput && !inputFull then
        some ((s.inputWanted.join.getD cfg.defaultPayloadBytes).min cfg.maximumRecvSize)
      else none
    -- While the caller is the one pausing, or the peer is taking our bytes, `requestTimeout` bounds
    -- the wait instead of `readTimeout`.
    let read := if recv.isSome && !awaitsCaller && s.writes == .idle then
      #[(Timer.read, Arm.within (millis cfg.readTimeout))] else #[]
    let cont := match ex.continueDeadline with
      | some deadline => #[(Timer.continue, Arm.until deadline)]
      | none => #[]
    { recv
      request := false
      requestBody := ex.upload == .open && !backlogged
      writesIdle := s.writes != .idle
      writesLate := s.writes != .idle
      responseInterest := pullable
      responseClosed := ex.download == .open && !pullable
      timers := read ++ (if s.writes == .idle then #[(.request, .until ex.deadline)] else #[]) ++ cont }

/--
The timer of `src` due first at `now`, with the milliseconds until it fires: the only one that can end
the wait.
-/
def Sources.due (src : Sources) (now : Nat) : Option (Timer × Nat) :=
  src.timers.foldl (init := none) fun due (timer, arm) =>
    let ms := match arm with
      | .until deadline => deadline - now
      | .within timeout => timeout
    match due with
    | some (_, earliest) => if ms < earliest then some (timer, ms) else due
    | none => some (timer, ms)

/-! ## Exchanges -/

/--
The length the caller sees for a response to `method`. A HEAD response, and a 1xx, 204 or 304, ends
at its header section whatever its framing fields say (RFC 9112 §6.3).
-/
def responseBodySize (method : Method) (head : Response.Head) : Option Body.Length :=
  if method == .head || head.status.isInformational || head.status == .noContent ||
      head.status == .notModified then
    some (.fixed 0)
  else H1.Message.Head.getSize (dir := .sending) head (allowEOFBody := false)

/-- The interim responses a request may receive before its final one. -/
def maxInterimResponses : Nat := 16

@[inline] private def State.modifyExchange (s : State) (f : Exchange → Exchange) : State :=
  { s with exchange := s.exchange.map f }

/-- Moves the exchange's deadline: it made progress at `now`. -/
@[inline] private def progress (s : State) (now : Nat) : State :=
  s.modifyExchange fun ex => { ex with deadline := now + millis ex.config.requestTimeout }

/--
Ends the exchange with `err`, if one runs. A failure once the caller holds the whole response ends
the connection, not the exchange, which is then complete.
-/
private def rejectExchange (s : State) (err : Client.Error) (cmds : Array Command) : State × Array Command :=
  match s.exchange with
  | some ex => ({ s with exchange := none }, cmds.push (if ex.responseComplete then .complete else .reject err))
  | none => (s, cmds)

/--
Ends the connection: no further requests, the exchange in flight fails, and the writes in flight
complete before the connection closes.
-/
private def finish (s : State) (cmds : Array Command) : State × Array Command :=
  let (s, cmds) := rejectExchange s (.closed "connection closed") cmds
  let cmds := if s.accepting then cmds.push .stopAccepting else cmds
  ({ s with stage := .flushing, accepting := false }, cmds.push .flush)

/-- Ends the exchange with `err` and the connection with it. -/
private def abort (s : State) (err : Client.Error) (cmds : Array Command) : State × Array Command :=
  let cmds := if s.accepting then cmds.push .stopAccepting else cmds
  let (s, cmds) := rejectExchange { s with accepting := false } err cmds
  finish { s with machine := s.machine.shutdown } cmds

/--
Stops the request body: the server answered before it was all sent, or its producer failed. The
message ends where it stands.
-/
private def abandonUpload (s : State) (cmds : Array Command) : State × Array Command :=
  match s.exchange with
  | some ex =>
    if ex.upload == .done then (s, cmds)
    else
      ({ s with
          machine := s.machine.abandonOutgoingBody
          exchange := some { ex with upload := .done, continueDeadline := none } },
        cmds.push .closeRequestBody)
  | none => (s, cmds)

/--
The caller has the whole response body. The exchange ends once the connection is done with it, and
the stream stays open until then, so a caller that reads the body to its end and sends again finds
the connection free; a request body still being produced could hold it long, so then the stream
closes at once.
-/
private def finishResponse (s : State) (cmds : Array Command) : State × Array Command :=
  match s.exchange with
  | some ex =>
    if ex.download == .done || ex.download == .held then (s, cmds)
    else
      let producing := ex.upload == .open && !s.machine.outgoingBodySupplied
      let ex := { ex with responseComplete := true, download := if producing then .done else .held }
      ({ s with exchange := some ex }, if producing then cmds.push .endResponse else cmds)
  | none => (s, cmds)

/-- Fails the exchange when its response body is over `maxResponseBodySize`. -/
private def checkBodyLimit (s : State) (cmds : Array Command) : Option (State × Array Command) :=
  match s.exchange with
  | some ex =>
    if ex.config.maxResponseBodySize.any (s.machine.bodyBytesRead > ·) then
      some (abort s .bodyLimitExceeded cmds)
    else none
  | none => none

/--
Settles the response body the caller closed: the machine drains it, within `maxResponseBodySize`.
What the machine holds may complete it; a body still arriving after that would hold the connection
for as long as the peer sends, so the connection ends. The commands are set when it does.
-/
private def settleDownload (s : State) : State × Option (Array Command) :=
  match s.exchange with
  | some ex =>
    if ex.download != .abandoned then (s, none)
    else
      let s := { s with machine := s.machine.drainBody }
      match checkBodyLimit s #[] with
      | some (s, cmds) => (s, some cmds)
      | none =>
        if s.machine.isReadingBody then
          let (s, cmds) := abort s (.closed "response body closed before it ended") #[]
          (s, some cmds)
        else (s, none)
  | none => (s, none)

/--
Records that the machine is done with the request body, as when an early final response ended the
connection while it was written (RFC 9112 §9.5).
-/
private def settleUpload (s : State) (cmds : Array Command) : State × Array Command :=
  match s.exchange with
  | some ex =>
    if ex.upload == .open && !s.machine.isWritingBody && s.machine.outgoingBodySupplied then
      ({ s with exchange := some { ex with upload := .done } }, cmds.push .closeRequestBody)
    else (s, cmds)
  | none => (s, cmds)

/-! ## Passes of the machine -/

/--
Decides whether the next input comes from the sources or the next pass of the machine.
-/
private def endPass (s : State) (cmds : Array Command) : State × Array Command :=
  let (s, cmds) := settleUpload s cmds
  if s.exchange.isNone && !s.accepting then finish s cmds else
  let m := s.machine
  let waits := !m.hasPendingEvents &&
    (s.inputWanted.isSome || s.exchange.isNone || m.canPullBody ||
      s.exchange.any (·.upload != .done))
  ({ s with stage := if waits then .polling else .running }, cmds)

/-- Applies a response head: an interim one, or the final one the caller gets. -/
private def receiveHead (now : Nat) (s : State) (head : Response.Head) (cmds : Array Command) :
    State × Array Command × Bool :=
  match s.exchange with
  | none => (s, cmds, false)
  | some ex =>
    if head.status.isInterim then
      let ex := { ex with interim := ex.interim + 1 }
      if ex.interim > maxInterimResponses then
        let (s, cmds) :=
          abort { s with exchange := some ex } (.protocol (.other "too many interim responses")) cmds
        (s, cmds, true)
      else if head.status == .continue && ex.upload == .parked then
        ({ s with exchange := some { ex with upload := .open, continueDeadline := none } },
          cmds.push (.interim head), false)
      else ({ s with exchange := some ex }, cmds.push (.interim head), false)
    else
      let (s, cmds) := if ex.upload == .parked then abandonUpload s cmds else (s, cmds)
      let s := s.modifyExchange ({ · with download := .open, finalHead := true })
      -- From the head on, `requestTimeout` bounds each pause in the body, not the exchange as a whole.
      let s := progress s now
      (s, cmds.push (.deliverHead head (responseBodySize ex.method head)), false)

/--
Processes the events of one pass of the machine, then ends the pass. A failure skips the events
after it. The event ending an exchange waits for the exchange's writes, unless they were `awaited`:
the next request cannot go out while a write of this one is in flight. The events before it do not
wait, so a response that answers a blocked upload early reaches the caller.
-/
private def processEvents (now : Nat) (awaited : Bool) (s : State) (cmds : Array Command) :
    List (H1.Event .sending) → State × Array Command
  | [] => endPass s cmds
  | event :: rest =>
    match event with
    | .needMoreData expect => processEvents now awaited { s with inputWanted := some expect } cmds rest
    | .needAnswer | .«continue» => processEvents now awaited s cmds rest
    | .endHeaders head =>
      match receiveHead now s head cmds with
      | (s, cmds, true) => (s, cmds)
      | (s, cmds, false) => processEvents now awaited s cmds rest
    | .closeBody =>
      let (s, cmds) := finishResponse s cmds
      processEvents now awaited s cmds rest
    | .next =>
      if !awaited && s.writes != .idle then
        -- The caller has the whole response, and the wait may last until the deadline.
        let (s, cmds) := match s.exchange with
          | some ex =>
            if ex.download == Download.held then
              (s.modifyExchange ({ · with download := .done }), cmds.push .endResponse)
            else (s, cmds)
          | none => (s, cmds)
        ({ s with stage := .writing (event :: rest) true }, cmds.push .awaitWritten)
      else
      -- Bytes buffered past this response answer no request this connection sent: reused, it would
      -- hand them to the next request as its response.
      let leftover := s.machine.hasBufferedInput
      let cmds := if s.exchange.isSome then cmds.push .complete else cmds
      let s := { s with exchange := none }
      if leftover then finish s cmds else processEvents now awaited s cmds rest
    | .failed err =>
      let cmds := if s.accepting then cmds.push .stopAccepting else cmds
      let err : Client.Error := match err with
        | .connectionClosed => .closed "connection closed"
        | err => .protocol err
      let (s, cmds) := rejectExchange { s with accepting := false } err cmds
      endPass { s with inputWanted := none } cmds
    | .close =>
      let cmds := if s.accepting then cmds.push .stopAccepting else cmds
      let s := { s with accepting := false }
      match s.exchange with
      | some ex =>
        if ex.responseComplete then
          processEvents now awaited { s with exchange := none } (cmds.push .complete) rest
        else if s.machine.error == some .badMessage then
          -- The writer refused the outgoing message: the request body did not match the length it
          -- declared. That is the request's fault, not the connection's, so it is not retried.
          let (s, cmds) :=
            rejectExchange s (.invalidRequest "the request body did not match its declared length") cmds
          processEvents now awaited s cmds rest
        else processEvents now awaited s cmds rest
      | none => processEvents now awaited s cmds rest

/--
Runs one pass of the machine and hands its output to the writes.
-/
private def pass (s : State) : State × Array Command :=
  match settleDownload s with
  | (s, some cmds) => (s, cmds)
  | (s, none) =>
    if s.machine.exhausted then finish s #[]
    else
      let (machine, result) := s.machine.step
      let s := { s with machine }
      let s := if result.output.size > 0 then s.modifyExchange ({ · with headSent := true }) else s
      ({ s with stage := .writing result.events.toList }, #[Command.write result.output])

/-! ## Inputs -/

/-- Starts the exchange of a request. -/
private def submit (cfg : Client.Config) (s : State) (now : Nat) (head : Request.Head)
    (size : Option Body.Length) (overrides : RequestOverrides) : State × Array Command :=
  if !s.idle then (s, #[.refuse (.notSent "the connection takes no request now")])
  else
    let cfg := overrides.apply cfg
    -- A request without content carries no `100-continue` expectation (RFC 9110 §10.1.1).
    let head :=
      if size matches some (.fixed 0) && H1.Message.Head.hasExpectContinue (dir := .receiving) head then
        { head with headers := head.headers.erase .expect }
      else head
    let machine := s.machine.sendRequest head size
    match machine.error with
    | some err =>
      -- The machine refused the head the caller built; it writes nothing and halts.
      ({ s with machine, accepting := false },
        #[.refuse (.invalidRequest (match err with | .other msg => msg | err => toString err)),
          .stopAccepting])
    | none =>
      let parked := machine.awaitsContinue
      let ex : Exchange := {
        method := head.method, config := cfg
        upload := if parked then .parked else .open
        deadline := now + millis cfg.requestTimeout
        continueDeadline := if parked then some (now + millis cfg.expectContinueTimeout) else none }
      ({ s with machine, exchange := some ex }, #[])

/-- Trailer fields as `Headers`, without those whose name or value is not a valid field. -/
private def trailerHeaders (fields : Array (String × String)) : Headers :=
  fields.foldl (init := .empty) fun headers (name, value) =>
    match Header.Name.ofString? name, Header.Value.ofString? value with
    | some name, some value => headers.insert name value
    | _, _ => headers

/-- Hands the caller the next response body chunk, when the machine holds one. -/
private def deliver (s : State) (now : Nat) : State × Array Command :=
  match s.machine.pullBody with
  | (machine, some pulled) =>
    let s := { s with machine }
    match checkBodyLimit s #[] with
    | some result => result
    | none =>
      let s := progress s now
      let cmds := #[Command.offerBody pulled.chunk pulled.final]
      if pulled.final then
        let (machine, fields) := s.machine.takeTrailers
        let cmds := if fields.isEmpty then cmds else cmds.push (.trailers (trailerHeaders fields))
        finishResponse { s with machine } cmds
      else (s, cmds)
  | (machine, none) => ({ s with machine }, #[])

/--
A write failed. Once the final head is in, the response no longer depends on the upload, so the rest
of it is dropped and the response finishes; the connection carries no further request, since the
peer never got this one whole. Otherwise the exchange fails.
-/
private def writeFailed (now : Nat) (s : State) (events : List (H1.Event .sending)) :
    State × Array Command :=
  if s.exchange.any (·.finalHead) then
    let cmds := if s.accepting then #[Command.stopAccepting] else #[]
    let (s, cmds) := abandonUpload { s with accepting := false } cmds
    processEvents now true s cmds events
  else abort s (.closed "connection write failed") #[]

/--
A write failed after its batch was reported, while the connection waits: as `writeFailed` with no
events left to process.
-/
private def writeFailedIdle (s : State) : State × Array Command :=
  if s.exchange.any (·.finalHead) then
    abandonUpload { s with accepting := false } (if s.accepting then #[.stopAccepting] else #[])
  else abort s (.closed "connection write failed") #[]

/--
Applies an input from the sources. Unless it ends the connection, the next pass of the machine
follows.
-/
private def apply (cfg : Client.Config) (s : State) (now : Nat) : Input → State × Array Command
  | .submit head size overrides => submit cfg s now head size overrides
  | .received (some data) =>
    match s.exchange with
    -- Bytes on an idle connection answer no request, as the `408` a server sends before closing an
    -- idle connection: fed to the machine, they would become the next request's response.
    | none => finish s #[]
    | some ex =>
      if !ex.headSent then
        abort s (.notSent "the peer sent a response before the request was written") #[]
      else ({ s with machine := s.machine.feed data }, #[])
  | .received none =>
    if s.exchange.any (!·.headSent) then
      abort s (.notSent "connection closed before the request was written") #[]
    else ({ s with machine := s.machine.noMoreInput }, #[])
  | .writesIdle => ({ progress s now with writes := .idle }, #[])
  | .pulled (some chunk) => ({ s with machine := s.machine.sendData #[chunk] }, #[])
  | .pulled none =>
    match s.machine.writer.state with
    | .writingBody (.fixed n) =>
      if s.machine.writer.userDataBytes < n then
        -- The caller's body broke its own `Content-Length`: the peer would wait for the rest.
        let (s', cmds) := abandonUpload s #[]
        abort s' (.invalidRequest
          s!"the request body ended {n - s.machine.writer.userDataBytes} bytes short of its length") cmds
      else
        ({ (s.modifyExchange ({ · with upload := .done, continueDeadline := none })) with
          machine := s.machine.userClosedBody },
        #[.closeRequestBody])
    | _ =>
      ({ (s.modifyExchange ({ · with upload := .done, continueDeadline := none })) with
        machine := s.machine.userClosedBody },
      #[.closeRequestBody])
  | .pullFailed err =>
    -- A request whose body was half written cannot be replayed, so it ends as the caller's failure,
    -- and the message is not framed as if the body had ended.
    let (s, cmds) := abandonUpload s #[]
    abort s (.io err) cmds
  | .bodyInterest true => deliver s now
  | .bodyInterest false =>
    (s.modifyExchange fun ex => if ex.download == .open then { ex with download := .abandoned } else ex, #[])
  | .fired .idle => finish s #[]
  | .fired .read | .fired .request => abort s .timeout #[]
  | .fired .continue =>
    -- The server never answered the expectation: the body goes as if it had (RFC 9110 §10.1.1). The
    -- deadline is cleared either way: left set, a past deadline would fire again at once.
    (s.modifyExchange fun ex =>
      { ex with
        upload := if ex.upload == .parked then .open else ex.upload
        continueDeadline := none }, #[])
  | .cancelled => abort s (.closed "connection shutdown") #[]
  | .failed err =>
    if s.exchange.any (·.upload == .open) then
      let (s, cmds) := abandonUpload s #[]
      abort s (.io err) cmds
    else abort s (.closed s!"connection read failed: {err}") #[]
  | .written false _ => writeFailedIdle s
  | .resume | .written .. => (s, #[])

/-! ## Stepping -/

/--
Answers an input at time `now`, in milliseconds of a monotonic clock: returns the new state and the
commands to perform, in order.
-/
def step (cfg : Client.Config) (s : State) (now : Nat) (input : Input) : State × Array Command :=
  match s.stage, input with
  | .closed, _ => (s, #[])
  | .flushing, .written .. => ({ s with stage := .closed }, #[.close])
  | .flushing, _ => (s, #[])
  | .writing events awaited, .written ok writes =>
    let s := { s with writes := if ok then writes else .idle }
    if ok then processEvents now awaited s #[] events else writeFailed now s events
  | .writing .., _ => (s, #[])
  | .polling, input =>
    let (s, cmds) := apply cfg { s with inputWanted := none } now input
    if s.stage matches .flushing then (s, cmds)
    else
      let (s, more) := pass s
      (s, cmds ++ more)
  | .running, _ => pass s

/-! ## Request policy -/

/--
The port an absolute-form target names for `origin`, omitted when it is the scheme's default so the
target reads the way the origin itself is written.
-/
private def absoluteFormPort (origin : URI.Origin) : URI.Port :=
  if origin.port == URI.Scheme.defaultPort origin.scheme then .omitted else .value origin.port

/--
The form `target` is sent in on a connection to `origin` through `proxy`: absolute-form through a
proxy, which RFC 9112 §3.2.2 requires there, and origin-form to the origin directly. Targets with no
path to re-address (authority-form, asterisk-form) are sent as they are.
-/
def requestTarget (proxy : Proxy) (origin : URI.Origin) (target : RequestTarget) : RequestTarget :=
  match proxy, target with
  | .direct, .absoluteForm uri => .originForm uri.path uri.query
  -- RFC 9110 §4.2.4 forbids userinfo in a target, and absolute-form (RFC 9112 §3.2.2) has no fragment.
  | .http .., .absoluteForm uri =>
    .absoluteForm { uri with
      authority := uri.authority.map ({ · with userInfo := none })
      fragment := none }
  | .http .., .originForm path query =>
    .absoluteForm {
      scheme := origin.scheme
      authority := some { host := origin.host, port := absoluteFormPort origin }
      path
      query
      fragment := none
    }
  | .direct, target | .http .., target => target

/--
The header fields a request to `origin` is sent with: the `Host` of the origin unless the caller
named one (RFC 9112 §3.2 requires the field, and only the connection knows the origin), and, when a
cookie handler gave `cookies`, one `Cookie` field joining them to any the caller attached.
-/
def requestHeaders (origin : URI.Origin) (headers : Headers) (cookies : Option (Array Header.Value)) :
    Headers :=
  let headers :=
    if headers.contains .host then headers else headers.insert .host (.ofString! origin.hostHeader)
  match cookies with
  | none => headers
  | some cookies =>
    let cookies := (headers.getAll? .cookie).getD #[] ++ cookies
    if cookies.isEmpty then headers
    else (headers.erase .cookie).insert .cookie
      (.ofString! (String.intercalate "; " (cookies.toList.map (·.value))))

/--
The kind of authentication challenge `status` carries on a connection through `proxy`, if any.
-/
def challengeKind? (proxy : Proxy) (status : Status) : Option Challenge.Kind :=
  if status == .unauthorized then some .server
  -- Only a proxy may ask for proxy credentials: an origin reached directly that answers `407` would
  -- otherwise be handed them.
  else if status == .proxyAuthenticationRequired && proxy != .direct then some .proxy
  else none

/--
`true` when an exchange ending in `head` leaves the connection able to carry another request: the
client allows reuse at all, the response did not ask for closure, and its body is framed by
something other than the connection close itself (RFC 9112 §6.3).
-/
def leavesConnectionReusable (config : Client.Config) (method : Method) (head : Response.Head) : Bool :=
  config.enableKeepAlive
  && H1.Message.Head.shouldKeepAlive (dir := .sending) head
  && (responseBodySize method head).isSome

end Std.Http.Client.Connection.Driver
