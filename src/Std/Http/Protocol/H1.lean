/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Init.Data.Array
public import Std.Http.Data
public import Std.Http.Internal
public import Std.Http.Protocol.H1.Parser
public import Std.Http.Protocol.H1.Config
public import Std.Http.Protocol.H1.Message
public import Std.Http.Protocol.H1.Reader
public import Std.Http.Protocol.H1.Writer
public import Std.Http.Protocol.H1.Event
public import Std.Http.Protocol.H1.Redirect
public import Std.Http.Protocol.H1.Rules
public import Std.Http.Protocol.H1.Encode

public section

/-!
# HTTP/1.1 Protocol State Machine

The sans-I/O HTTP/1.1 machine of one connection, for a server (`.receiving`: it reads requests and
writes responses) or a client (`.sending`). It holds the exchange in progress (`request` and
`response`), the incoming side (`Reader`) and the outgoing side (`Writer`). Every transition is a
total function of the machine. The rules that depend on a message head alone are in `H1.Rules`, the
encoding of heads in `H1.Encode`, and the grammar and input scanners in `H1.Parser`.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std Std.Internal Http.Internal Parsec ByteArray Rules Encode

/--
Results from a single step of the state machine.
-/
structure StepResult (dir : Direction) where
  /-- Events of this step. -/
  events : Array (Event dir) := #[]
  /-- Output ready for the transport. -/
  output : ChunkedBuffer := .empty

/--
A single body chunk produced by a pull-driven read.
-/
structure PulledChunk where
  /-- Whether this chunk finishes the body. -/
  final : Bool
  /-- Whether more bytes of the current chunk of a chunked body are still to come. -/
  incomplete : Bool
  /--
  The chunk. Chunked framing is removed; other transfer codings, such as the `gzip` of
  `Transfer-Encoding: gzip`, are not decoded. A server rejects a request with a coding that is not
  in `Config.acceptedTransferCodings`.
  -/
  chunk : Chunk

/--
The HTTP/1.1 protocol state machine.
-/
structure Machine (dir : Direction) where
  /-- The incoming side. -/
  reader : Reader := match dir with | .receiving => {} | .sending => { state := .pending }
  /-- The outgoing side. -/
  writer : Writer := match dir with | .receiving => {} | .sending => { state := .waitingHeaders }
  /-- The configuration. -/
  config : Config
  /-- The request of the exchange in progress: read by a server, written by a client. -/
  request : Request.Head := { method := .get, version := .v11 }
  /-- The response of the exchange in progress: written by a server, read by a client. -/
  response : Response.Head := {}
  /-- Events not taken yet. -/
  events : Array (Event dir) := #[]
  /-- The failure of the machine. -/
  error : Option Error := none
  /--
  The `Date` field value a server writes in each final response whose head has none, including the
  error responses the machine writes itself (RFC 9110 §6.6.1). The caller keeps it current; with
  `none`, no `Date` is added.
  -/
  date : Option Header.Value := none
  /-- Whether the connection is kept alive after the exchange. Only ever lowered. -/
  keepAlive : Bool := config.enableKeepAlive
  /-- The last `pullBody` could not make progress in a body; cleared by new input. -/
  pullBodyStalled : Bool := false

namespace Machine

@[inline] private def isServer (_ : Machine dir) : Bool :=
  dir matches .receiving

@[inline] private def modifyWriter (machine : Machine dir) (fn : Writer → Writer) : Machine dir :=
  { machine with writer := fn machine.writer }

@[inline] private def setReaderState (machine : Machine dir) (state : Reader.State) : Machine dir :=
  { machine with reader.state := state }

@[inline] private def setWriterState (machine : Machine dir) (state : Writer.State) : Machine dir :=
  { machine with writer.state := state }

@[inline] private def addEvent (machine : Machine dir) (event : Event dir) : Machine dir :=
  { machine with events := machine.events.push event }

/-- Every change of `keepAlive` within an exchange goes through here: it stays on while `keep`. -/
@[inline] private def lowerKeepAlive (machine : Machine dir) (keep : Bool) : Machine dir :=
  { machine with keepAlive := machine.keepAlive && keep }

@[inline] private def emit (machine : Machine dir) (bytes : ByteArray) : Machine dir :=
  machine.modifyWriter fun w => { w with outputData := w.outputData.push bytes }

@[inline] private def incoming (machine : Machine dir) : Message.Head dir :=
  match dir with
  | .receiving => machine.request
  | .sending => machine.response

@[inline] private def addBodyBytes (machine : Machine dir) (bytes : Nat) : Machine dir :=
  { machine with reader.bodyBytesRead := machine.reader.bodyBytesRead + bytes }

@[inline] private def fitsBodyLimit (machine : Machine dir) (extra : Nat) : Bool :=
  machine.reader.bodyBytesRead + extra ≤ machine.config.maxBodySize

/-- Records `error` and emits `.failed`; the connection is not reused. -/
@[inline] private def recordFailure (machine : Machine dir) (error : H1.Error) : Machine dir :=
  { machine.addEvent (.failed error) with error := some error, keepAlive := false }

/--
Fails on the incoming message and closes the reader. The message's framing is lost, so the
connection is not reused (RFC 9112 §6.3 rule 5, §8). A server answers it in `answerFailure`.
-/
@[inline] private def setFailure (machine : Machine dir) (error : H1.Error) : Machine dir :=
  (machine.recordFailure error).setReaderState .closed

/-- The body being read belongs to an interim (1xx) response, which is not the exchange's. -/
@[inline] private def isInterimResponseBody (machine : Machine dir) : Bool :=
  !machine.isServer && machine.response.status.isInterim

/--
Body chunks are drained internally rather than handed out. A server drains the rest of a request
body once its response is written (until then the handler may be reading it, say to stream it back),
and an empty remainder as soon as the response head is sent.
-/
@[inline] private def drainBodyInternally (machine : Machine dir) : Bool :=
  if machine.isServer then
    (machine.writer.state matches .complete | .closed) ||
      (machine.writer.sentMessage && machine.reader.state matches .readBody (.fixed 0))
  else machine.isInterimResponseBody

/-- Returns `true` if the machine failed. `error` holds the cause. -/
@[inline] def failed (machine : Machine dir) : Bool :=
  machine.error.isSome

/-- Returns `true` if the reader has read a whole message and waits for the exchange to end. -/
@[inline] def isReaderComplete (machine : Machine dir) : Bool :=
  machine.reader.state matches .complete

/-- Returns `true` if the reader is closed. -/
@[inline] def isReaderClosed (machine : Machine dir) : Bool :=
  machine.reader.state matches .closed

/-- Returns `true` when a server's reader waits for a `canContinue` decision. -/
@[inline] def isReaderAwaitingContinue (machine : Machine dir) : Bool :=
  machine.isServer && machine.reader.state matches .continue _

/-- Returns `true` if the head waiting in the writer should be written now. -/
@[inline] def shouldFlush (machine : Machine dir) : Bool :=
  machine.failed ||
  -- A server's reader closes after a request that ends the connection, which says nothing about the
  -- response body: its head waits like any other, so a body that fails first can still get a 500.
  (!machine.isServer && machine.reader.state matches .closed) ||
  machine.writer.noMoreUserData || machine.writer.knownSize.isSome ||
  -- Body bytes go out as soon as they exist, except for an HTTP/1.0 request, which cannot be chunked
  -- (RFC 9112 §6.1), so it waits for its whole body, whose length its head must carry.
  (machine.writer.userData.size > 0 && !(!machine.isServer && machine.request.version == .v10))

/-- Returns `true` if the writer waits for the head of a message (`send`). -/
@[inline] def isWaitingMessage (machine : Machine dir) : Bool :=
  machine.writer.state matches .waitingHeaders

/-- Returns `true` if both sides are closed and no output remains. -/
@[inline] def halted (machine : Machine dir) : Bool :=
  machine.reader.state matches .closed && machine.writer.state matches .closed &&
    machine.writer.outputData.isEmpty

/-- Returns `true` when `pullBody` can attempt to produce body data. -/
@[inline] def canPullBody (machine : Machine dir) : Bool :=
  !drainBodyInternally machine && machine.reader.state matches .readBody _

/-- Returns `true` when `pullBody` is expected to make progress. -/
@[inline] def canPullBodyNow (machine : Machine dir) : Bool :=
  machine.canPullBody && !machine.pullBodyStalled

/-- Returns `true` while the reader holds input it has not parsed yet. -/
@[inline] def hasBufferedInput (machine : Machine dir) : Bool :=
  !machine.reader.input.atEnd

/-- The number of input bytes the reader holds and has not parsed yet. -/
@[inline] def bufferedInputBytes (machine : Machine dir) : Nat :=
  machine.reader.input.remainingBytes

/--
The decoded body bytes accepted for the current incoming message. Bytes the machine drains by
itself count as well as those `pullBody` hands out, so a caller enforcing its own body limit gets
the same total whether or not it reads the body.
-/
@[inline] def bodyBytesRead (machine : Machine dir) : Nat :=
  machine.reader.bodyBytesRead

/--
Returns `true` while the machine still takes input: the peer has not closed its side and the
machine has not stopped reading.
-/
@[inline] def needsInput (machine : Machine dir) : Bool :=
  !machine.reader.noMoreInput

/--
Returns `true` when the machine has no work left and never will: it halted, or it takes no more
input, has no body left to hand out, no unparsed input its reader can still read, and no events.
-/
@[inline] def exhausted (machine : Machine dir) : Bool :=
  machine.halted ||
    (!machine.needsInput && !machine.canPullBodyNow && machine.events.isEmpty &&
      (machine.isReaderClosed || !machine.hasBufferedInput))

/-- Returns `true` when events of an earlier step are still queued. -/
@[inline] def hasPendingEvents (machine : Machine dir) : Bool :=
  !machine.events.isEmpty

/--
Applies the result of a parser run on the input, which held `remaining` bytes. On success the input
advances, unless the parser consumed more than `limit` bytes. Input that ends inside the line asks
for more data, unless none will come or `limit` bytes are already buffered. Other parse errors fail
with `onHardError`.
-/
@[inline] private def applyParse (machine : Machine dir) (remaining : Nat)
    (result : ParseResult α ByteArray.Iterator) (limit : Option Nat)
    (onHardError : Std.Internal.Parsec.Error → H1.Error) : Machine dir × Option α :=
  match result with
  | .success rest result =>
    if limit.any (remaining - rest.remainingBytes > ·) then (machine.setFailure .badMessage, none)
    else ({ machine with reader.input := rest }, some result)
  | .error it .eof =>
    if machine.reader.noMoreInput then (machine.setFailure .connectionClosed, none)
    else if limit.any (remaining - it.remainingBytes ≥ ·) then (machine.setFailure .badMessage, none)
    else (machine.addEvent (.needMoreData none), none)
  | .error _ err => (machine.setFailure (onHardError err), none)

/--
`parseLine` with an active scan (`LineScan.read`, unfolded): the parser runs only where the scan
stops, or on the whole line when the scan cannot resume.
-/
@[specialize]
private def parseLineScanned (machine : Machine dir) (kind : LineKind) (parser : Parser α)
    (limit : Option Nat) (onHardError : Std.Internal.Parsec.Error → H1.Error) :
    Machine dir × Option α :=
  let reader := machine.reader
  let input := reader.input
  let remaining := input.remainingBytes
  let scan := reader.lineScan
  let resumes := scan.resumes kind reader.noMoreInput limit input
  let (scan, stopped) := if resumes then scan.advance machine.config false input else (scan, true)
  if !stopped then
    ({ machine with reader.lineScan := scan, events := machine.events.push (.needMoreData none) },
      none)
  else
    match parser input with
    | .error it .eof =>
      let scan :=
        if resumes then (scan.advance machine.config true input).1
        else scan.afterEof machine.config kind input
      applyParse { machine with reader.lineScan := scan } remaining (.error it .eof) limit onHardError
    | result => applyParse { machine with reader.lineScan := {} } remaining result limit onHardError

/-- `parseLine` after a parser `.eof` at `it` on a line read from its start: keeps the scan. -/
private def parseLineEof (machine : Machine dir) (kind : LineKind) (remaining : Nat)
    (it : ByteArray.Iterator) (limit : Option Nat) : Machine dir × Option α :=
  let lineScan := machine.reader.lineScan.afterEof machine.config kind machine.reader.input
  applyParse { machine with reader.lineScan := lineScan } remaining (.error it .eof) limit
    (fun _ => .badMessage)

/--
Reads the line of `kind` at the start of the input with `parser`, resuming the scan of a line still
incomplete, so a line fed in pieces is not parsed again from its start on every read (#16522).
-/
@[inline] private def parseLine (machine : Machine dir) (kind : LineKind) (parser : Parser α)
    (limit : Option Nat)
    (onHardError : Std.Internal.Parsec.Error → H1.Error := fun _ => .badMessage) :
    Machine dir × Option α :=
  if machine.reader.lineScan.active then
    parseLineScanned machine kind parser limit onHardError
  else
    let input := machine.reader.input
    let remaining := input.remainingBytes
    match parser input with
    | .error it .eof => parseLineEof machine kind remaining it limit
    | result =>
      -- The complete-line path updates the reader only when a scan is left to clear.
      let machine :=
        if machine.reader.lineScan.inProgress then { machine with reader.lineScan := {} } else machine
      applyParse machine remaining result limit onHardError

/--
Ends the exchange: with keep-alive both sides start the next one, keeping unread input and unsent
output, and `.next` is emitted; otherwise both close and `.close` is emitted.
-/
private def resetForNextMessage (machine : Machine dir) : Machine dir :=
  if machine.keepAlive then
    let { input, messageCount, peerClosed, inputStopped, .. } := machine.reader
    let fresh : Machine dir := { config := machine.config }
    { machine with
      reader := { fresh.reader with input, messageCount := messageCount + 1, peerClosed, inputStopped }
      writer := { fresh.writer with outputData := machine.writer.outputData }
      request := fresh.request, response := {}
      events := machine.events.push .next, error := none, pullBodyStalled := false }
  else
    machine.addEvent .close |>.setWriterState .closed |>.setReaderState .closed

/--
Starts the body after a valid header section and emits `.endHeaders`. A server waits for an answer,
and first for the `canContinue` decision when the request has `Expect: 100-continue`.
-/
private def startBody (machine : Machine dir) (body : Reader.BodyState) : Machine dir :=
  let machine := machine.addEvent (.endHeaders machine.incoming)
  if machine.isServer then
    let expect := Message.Head.hasExpectContinue (dir := .receiving) machine.request
    let machine := if expect then machine.addEvent .continue else machine
    { machine with
      reader.state := if expect then .continue body else .readBody body
      writer.state := .waitingHeaders }
    |>.addEvent .needAnswer
  else
    machine.setReaderState (.readBody body)

/--
Ends a header section: lowers keep-alive as the head and the limits say, checks the head and
selects the body framing.
-/
private def processHeaders (machine : Machine dir) : Machine dir :=
  -- A client may send tunnel bytes right after `CONNECT`, before it reads the answer, so whatever
  -- the server answers, the bytes after the head are not read as another request (RFC 9110 §9.3.6).
  let machine := machine.lowerKeepAlive <|
    machine.reader.messageCount + 1 < machine.config.maxMessages &&
    Message.Head.shouldKeepAlive machine.incoming &&
    !(machine.isServer && machine.request.method == .connect)
  let checked :=
    if machine.isServer then checkReceivingMessageHead machine.config machine.request
    else checkSendingMessageHead machine.request.method machine.response
  match checked with
  | .error err => machine.setFailure err
  | .ok (.fixed n) =>
    if n > machine.config.maxBodySize then machine.setFailure .entityTooLarge
    else machine.startBody (.fixed n)
  | .ok .chunked => machine.startBody .chunkedSize
  | .ok .eof => (machine.lowerKeepAlive false).startBody .closeDelimited

/--
Writes the outgoing head and selects the body framing: the length the caller set, else the whole
body once the caller closed it, else chunked. A server answering HTTP/1.0 replaces chunked by
close-delimited framing (RFC 9112 §6.1), which ends the connection unless the body is omitted.
-/
private def writeHead (machine : Machine dir) : Machine dir :=
  -- A final response written while the `100-continue` decision is pending ends the exchange without
  -- the body (`processCompleteStep`), so its head says `close` (RFC 9110 §10.1.1).
  let outgoingKeepsAlive :=
    if machine.isServer then Message.Head.shouldKeepAlive (dir := .sending) machine.response
    else Message.Head.shouldKeepAlive (dir := .receiving) machine.request
  let machine := machine.lowerKeepAlive <|
    machine.reader.messageCount + 1 < machine.config.maxMessages && outgoingKeepsAlive &&
    !machine.isReaderAwaitingContinue
  let writer := machine.writer
  let size : Body.Length :=
    -- RFC 9110 §15.3.6: a 205 response is framed as empty, whatever length was set for its body.
    if machine.isServer && machine.response.status == .resetContent then .fixed 0
    -- RFC 9110 §9.3.6: whatever length was set since `send`, a CONNECT request has no content.
    else if !machine.isServer && machine.request.method == .connect then .fixed 0
    else writer.knownSize.getD (if writer.userClosedBody then .fixed writer.userDataBytes else .chunked)
  let raw := machine.isServer && machine.request.version == .v10 && size matches .chunked
  let machine := machine.lowerKeepAlive (!raw || writer.omitBody)
  let encoded :=
    if machine.isServer then
      encodeServerHead machine.response machine.request.version machine.keepAlive machine.date
        machine.config.agentName size (startsTunnel machine.request.method machine.response.status)
    else
      encodeClientHead machine.request machine.keepAlive machine.config.agentName size
  let body : Writer.BodyState :=
    match size with
    | .fixed n => .fixed n
    | .chunked => if raw then .closeDelimited else .chunked
  -- `readStep` does this first when `step` drives the machine; `processWrite` alone needs it here.
  let machine :=
    if !machine.isServer && machine.reader.state matches .pending then
      machine.setReaderState .needStartLine
    else machine
  machine.modifyWriter fun w =>
    { w with outputData := w.outputData.push encoded, state := .writingBody body }

/-- Feeds input bytes to the reader. -/
@[inline] def feed (machine : Machine dir) (data : ByteArray) : Machine dir :=
  if machine.isReaderClosed || machine.failed then
    machine
  else
    let machine := { machine with reader := machine.reader.feed data, pullBodyStalled := false }
    let config := machine.config
    if machine.reader.remainingBytes > config.maxBufferedBodyBytes.getD config.maxBodySize +
        config.maxHeaderBytes + config.maxStartLineLength + config.maxChunkLineLength then
      machine.setFailure .entityTooLarge
    else
      machine

/--
Stops taking input without changing the reader state: input already buffered is still parsed, then
the reader ends as at EOF.
-/
@[inline] def closeReader (machine : Machine dir) : Machine dir :=
  { machine with reader.inputStopped := true, pullBodyStalled := false }

/-- Closes the writer: no more output. -/
@[inline] def closeWriter (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with state := .closed, userClosedBody := true })

/-- Signals that the caller handed over the whole outgoing body. -/
@[inline] def userClosedBody (machine : Machine dir) : Machine dir :=
  { machine with writer.userClosedBody := true }

/--
Takes the trailer fields of the incoming message read so far (see `Reader.trailers`), leaving none.
-/
@[inline] def takeTrailers (machine : Machine dir) : Machine dir × Array (String × String) :=
  ({ machine with reader.trailers := #[] }, machine.reader.trailers)

/-- Signals that the peer closed its side of the connection, so no more input will arrive. -/
@[inline] def noMoreInput (machine : Machine dir) : Machine dir :=
  { machine with reader.peerClosed := true, pullBodyStalled := false }

/--
Stops the machine in both directions, as when the connection is torn down outside the protocol (a
timeout or a transport failure): no more output, and no more input.
-/
@[inline] def shutdown (machine : Machine dir) : Machine dir :=
  machine.closeWriter.closeReader

/-- Sets the length of the outgoing body, replacing any previous value. -/
@[inline] def setKnownSize (machine : Machine dir) (size : Body.Length) : Machine dir :=
  machine.modifyWriter fun w =>
    { w with framing := if w.omitBody then .omitted (some size) else .known size }

/--
Writes no body bytes for the current outgoing message; its head is still written. With
`forceZero`, the head advertises an empty body.
-/
@[inline] def suppressOutgoingBody (machine : Machine dir) (forceZero : Bool := false) :
    Machine dir :=
  machine.modifyWriter fun w =>
    { w with
      framing := .omitted (if forceZero then some (.fixed 0) else w.knownSize)
      userClosedBody := true, userData := #[], userDataBytes := 0 }

/--
Rejects a head the sender's own code got wrong; none of that message is written. A server answers
`500 Internal Server Error` and closes the connection, a client ends the exchange. Both report
`error`, and the machine halts once its output is taken.
-/
private def rejectOutgoing (machine : Machine dir) (error : H1.Error) : Machine dir :=
  let machine := (machine.recordFailure error).closeReader.setReaderState .closed
  if machine.isServer then
    -- Written here, not by the writer, which drops omitted content: the body is omitted so that the
    -- connection drops the handler's body instead of draining it.
    let content := errorContent .internalServerError
    let head := errorHead .internalServerError
    let machine := machine.emit <| encodeServerHead head machine.request.version machine.keepAlive
      machine.date machine.config.agentName (.fixed content.size)
    -- RFC 9110 §9.3.2: a HEAD response keeps the `Content-Length` but carries no content.
    let machine := if machine.request.method == .head then machine else machine.emit content
    { machine with response := head, writer.state := .complete }.suppressOutgoingBody
  else
    machine.closeWriter

/--
Adopts the framing fields of a final head: `fields` says whether it has any, `size` the length they
give. The fields' length is adopted when none was set, or only `chunked` (unknown length, as a
`Body.stream` starts). `none` when the two contradict, or the fields describe no length, unless no
body goes out (`omits`), which nothing can contradict.
-/
private def adoptFraming (machine : Machine dir) (fields : Bool) (size : Option Body.Length)
    (omits : Bool) : Option (Machine dir) :=
  match size, machine.writer.knownSize with
  | some parsed, some explicit =>
    if omits || explicit == .chunked then some (machine.setKnownSize parsed)
    else if explicit == parsed then some machine
    -- The fixed-length writer closes the connection if the body then runs over or falls short.
    else none
  | some parsed, none => some (machine.setKnownSize parsed)
  | none, _ => if fields && !omits then none else some machine

/--
`send` for a server. A 1xx head is written at once without framing fields, or dropped for an
HTTP/1.0 request (RFC 9110 §15.2), and the writer keeps waiting for the final head. A final head
without content (to `HEAD`, a 1xx/204/205/304, or a 2xx to `CONNECT`) omits the body; a 2xx to
`CONNECT` also closes the connection, since this server does not tunnel.
-/
private def sendResponseHead (machine : Machine .receiving) (head : Response.Head) :
    Machine .receiving :=
  let request := machine.request
  if head.status.isInformational then
    if request.version != .v11 then machine
    else
      -- Like a final head, an interim head says HTTP/1.1 (RFC 9110 §6.2), and a `close` in it ends
      -- the connection after this exchange (RFC 9112 §9.6).
      let head := { head with
        version := .v11
        headers := head.headers.erase .contentLength |>.erase .transferEncoding }
      (machine.lowerKeepAlive (Message.Head.shouldKeepAlive (dir := .sending) head)).emit
        (ByteArray.empty ++ head)
  else
    let fields := hasFramingHeaders (dir := .sending) head
    let tunnel := startsTunnel request.method head.status
    let noContent := responseOmitsContent head.status || tunnel
    let omits := noContent || request.method == .head
    -- HTTP/1.0 defines no transfer coding (RFC 9112 §6.1), so content still coded cannot be framed.
    let coded := request.version == .v10 &&
      match head.headers.getAll? .transferEncoding >>= Header.TransferEncoding.parseFieldLines? with
      | some codings => codings.any (· != "chunked")
      | none => false
    let size := if fields then Message.Head.getSize (dir := .sending) head false else none
    match machine.adoptFraming fields size omits with
    | some machine =>
      if coded && !omits then machine.rejectOutgoing framingMismatchError else
      let machine := { machine with response := head, writer.state := .waitingForFlush }
      let machine :=
        if !omits then machine
        else
          -- RFC 9110 §9.3.2: a HEAD response has the framing fields GET would have. With no known
          -- length that is chunked framing, not the `Content-Length: 0` of a body closed empty.
          let machine :=
            if !noContent && machine.writer.knownSize.isNone then machine.setKnownSize .chunked
            else machine
          machine.suppressOutgoingBody (responseForbidsFramingHeaders head.status || tunnel)
      if tunnel then (machine.lowerKeepAlive false).closeReader.setReaderState .closed else machine
    | none => machine.rejectOutgoing framingMismatchError

/--
`send` for a client. A head `requestHeadError?` refuses is not written, and neither is a chunked
HTTP/1.0 request (RFC 9112 §6.1). A `CONNECT` request has no content (RFC 9110 §9.3.6), so its head
goes out at once, and one whose fields announce content is refused. The reader waits for the head to
be written: until then, a response answers no request (RFC 9112 §9.2).
-/
private def sendRequestHead (machine : Machine .sending) (head : Request.Head) : Machine .sending :=
  if let some error := requestHeadError? head then machine.rejectOutgoing error else
  let machine := if head.method == .connect then machine.setKnownSize (.fixed 0) else machine
  let fields := hasFramingHeaders (dir := .receiving) head
  let size := if fields then Message.Head.getSize (dir := .receiving) head false else none
  match machine.adoptFraming fields size false with
  | some machine =>
    if head.version == .v10 && machine.writer.knownSize == some .chunked then
      machine.rejectOutgoing framingMismatchError
    else
      { machine with request := head, writer.state := .waitingForFlush }
  | none => machine.rejectOutgoing framingMismatchError

/--
Sends the head of the outgoing message. Does nothing unless `isWaitingMessage`.

A server writes a 1xx head at once (dropped for HTTP/1.0) and keeps waiting for the final one;
`canContinue`, not `send`, resolves `Expect: 100-continue`. A `Content-Length` in the head gives the
length of a body set as `chunked`. A head whose framing fields otherwise contradict `setKnownSize`, or
describe no length, or that HTTP/1.0 cannot frame, is not written: a server answers `500 Internal
Server Error`, a client ends the exchange; both report an `.other` error and halt. A client does the
same with a request head that `requestHeadError?` refuses, and writes no content for `CONNECT`
(RFC 9110 §9.3.6). A response without content (to `HEAD`, 1xx/204/205/304, a 2xx to `CONNECT`)
cannot contradict it; a HEAD response advertises its head's `Content-Length`, and a 2xx to `CONNECT`
closes the connection after its head.
-/
@[inline] def send (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  if !machine.isWaitingMessage then
    machine
  else
    match dir with
    | .receiving => machine.sendResponseHead message
    | .sending => machine.sendRequestHead message

/-- Hands body chunks to the writer. -/
@[inline] def sendData (machine : Machine dir) (data : Array Chunk) : Machine dir :=
  if data.isEmpty then
    machine
  else
    machine.modifyWriter fun w =>
      { w with
        userData := w.userData ++ data
        userDataBytes := data.foldl (· + ·.data.size) w.userDataBytes }

/--
Sends the final response to the request: its head, and the length of its body when `size` gives
it. A 1xx status cannot be final (RFC 9110 §15.2): the machine answers `500 Internal Server Error`
instead and reports the mistake, as for a head that contradicts its body. Does nothing unless the
machine waits for a response head.
-/
def sendResponse (machine : Machine .receiving) (head : Response.Head) (size : Option Body.Length) :
    Machine .receiving :=
  if !machine.isWaitingMessage then
    machine
  else if head.status.isInformational then
    machine.rejectOutgoing (.other s!"the final response has the interim status {head.status.toCode}")
  else
    (size.elim machine machine.setKnownSize).send head

/--
Sends a response the machine writes itself, with `errorContent` as `text/plain` content (RFC 9110
§15.5, §15.6); to `HEAD` without the content. Does nothing once a response is under way.
-/
private def sendError (machine : Machine .receiving) (status : Status) (headers : Headers := .empty) :
    Machine .receiving :=
  if !machine.isWaitingMessage then
    machine
  else
    let content := errorContent status
    machine
    |>.setKnownSize (.fixed content.size)
    |>.sendData #[{ data := content }]
    |>.send (errorHead status headers)
    |>.userClosedBody

/--
Sends a request head and fixes the framing of its body.

`knownSize` is the body length the caller knows up front. When neither it nor the head's framing
fields give a length and the request has `Expect: 100-continue`, the body is chunked: the head must
go out before the interim response arrives, so there is no chance to compute a `Content-Length`.
-/
def sendRequest (machine : Machine .sending) (head : Message.Head .receiving)
    (knownSize : Option Body.Length) : Machine .sending :=
  let machine := machine.send head
  match knownSize with
  | some size => machine.setKnownSize size
  | none =>
    if Message.Head.hasExpectContinue (dir := .receiving) head && machine.writer.knownSize.isNone then
      machine.setKnownSize .chunked
    else
      machine

/--
Returns `true` when the request being written has `Expect: 100-continue`, so its body waits until
the server sends an interim response or the caller stops waiting for one.
-/
@[inline] def awaitsContinue (machine : Machine .sending) : Bool :=
  Message.Head.hasExpectContinue (dir := .receiving) machine.request

/--
Resolves an `Expect: 100-continue` decision. With `100 Continue` the interim response is written
and the body is read. Any other status is sent as the response (typically 417), with a short
`text/plain` explanation unless a final response was already sent; keep-alive ends and the reader
closes, so the body is never read.
-/
def canContinue (machine : Machine dir) (status : Status) : Machine dir :=
  match dir, machine.reader.state with
  | .receiving, .continue body =>
    if status == .continue then
      { machine.emit (ByteArray.empty ++ ({ status := .continue } : Response.Head)) with
        reader.state := .readBody body }
    else
      (machine.sendError status |>.lowerKeepAlive false).closeReader.setReaderState .closed
  | _, _ => machine

/--
Ends the exchange from the server's side, as on a timeout or a shutdown, and closes the reader:
input not yet read, including the rest of the request, is never parsed.

If no response head was written yet, including one sent but not flushed, `status` is sent in its
place with `Connection: close` and a short `text/plain` explanation. Otherwise the writer closes and
keep-alive ends.
-/
def closeWithError (machine : Machine .receiving) (status : Status) : Machine .receiving :=
  let unwritten := machine.writer.state matches .waitingForFlush
  let machine :=
    if machine.isWaitingMessage || unwritten then
      let machine :=
        if unwritten then
          machine.modifyWriter fun w => { w with
            state := .waitingHeaders, userData := #[], userDataBytes := 0, framing := .unset
            userClosedBody := false }
        else machine
      machine.sendError status (.empty |>.insert .connection (.mk "close"))
    else
      (machine.lowerKeepAlive false).closeWriter
  machine.closeReader.setReaderState .closed

/-- Takes the queued events. -/
@[inline] def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/-- Takes the output. -/
@[inline] def takeOutput (machine : Machine dir) : Machine dir × ChunkedBuffer :=
  ({ machine with writer.outputData := .empty }, machine.writer.outputData)

/--
The outgoing message on the wire is cut short (a fixed-length body ran over or fell short): the
connection closes with `.failed` and `.close`, which a server reports to `Handler.onFailure`.
-/
private def closeOnBadMessage (machine : Machine dir) : Machine dir :=
  (machine.recordFailure .badMessage).closeWriter.closeReader.setReaderState .closed |>.addEvent .close

/--
Input that reaches a client before its request head is written answers no request (RFC 9112 §9.2),
and what follows a response must not be read as the next one (RFC 9112 §6.3). Empty lines alone are
discarded (`skipEmptyLines`); anything else, a bare `CR` included (RFC 9112 §2.2), leaves the message
boundaries ambiguous, so the connection fails.
-/
private def readIdleInput (machine : Machine dir) : Machine dir :=
  let input := machine.reader.input
  if input.atEnd then machine
  else
    let rest := skipEmptyLines input
    if rest.atEnd || (isLoneCR rest && !machine.reader.noMoreInput) then
      { machine with reader.input := rest }
    else closeOnBadMessage machine

-- Out of line, so that `processWrite` does not take the machine apart on its idle paths.
private def closeWriterOnly (machine : Machine dir) : Machine dir :=
  machine.closeWriter

private def closeExchange (machine : Machine dir) : Machine dir :=
  machine.setWriterState .closed |>.addEvent .close

/--
Ends the exchange once the outgoing message is written: the next one starts when the incoming one
was read too and keep-alive holds. A final response written while the `canContinue` decision is
pending means the body will never be read, so the connection closes.
-/
private def processCompleteStep (machine : Machine dir) : Machine dir :=
  match machine.reader.state with
  | .complete =>
    if !machine.keepAlive then closeExchange machine
    else if machine.isServer then resetForNextMessage machine
    else
      let machine := readIdleInput machine
      if machine.isReaderComplete then resetForNextMessage machine else machine
  | .closed => closeExchange machine
  | .continue _ => closeExchange (machine.closeReader.setReaderState .closed)
  | _ => if machine.keepAlive then machine else closeExchange machine

@[inline] private def completeWriterMessage (machine : Machine dir) : Machine dir :=
  processCompleteStep (machine.setWriterState .complete)

/--
Writes the body as far as the buffered data allows, and completes the message once the caller closed
the body. An omitted body is dropped. A fixed-length body must get exactly its length: more bytes, or
fewer once the body is closed, close the connection, so the peer never reads a wrong body as whole.
-/
private def processBody (machine : Machine dir) : Machine dir :=
  let writer := machine.writer
  if writer.omitBody then
    completeWriterMessage (machine.modifyWriter ({ · with userData := #[], userDataBytes := 0 }))
  else
    match writer.state with
    | .writingBody (.fixed n) =>
      let bytes := writer.userDataBytes
      if bytes > n then closeOnBadMessage machine
      -- The last bytes wait for the body to close, so a late extra chunk is still caught.
      else if !writer.userClosedBody && (writer.userData.isEmpty || (bytes = n && n > 0)) then machine
      else
        let machine := { machine with
          writer := { writer.writeRawBody with state := .writingBody (.fixed (n - bytes)) } }
        if !writer.userClosedBody then machine
        else if bytes = n then completeWriterMessage machine
        -- Short of the length, it is reported in this step: the caller may not step again.
        else closeOnBadMessage machine
    | .writingBody .chunked =>
      let machine := machine.modifyWriter Writer.writeChunkedBody
      if writer.userClosedBody then completeWriterMessage (machine.emit "0\r\n\r\n".toUTF8)
      else machine
    | .writingBody .closeDelimited =>
      let machine := machine.modifyWriter Writer.writeRawBody
      if writer.userClosedBody then completeWriterMessage machine else machine
    | _ => machine

/--
One transition of the writer: a client asks for the next request, a head waiting for `shouldFlush`
is written with as much body as there is, a body is written, a completed message ends the exchange.
-/
def processWrite (machine : Machine dir) : Machine dir :=
  match machine.writer.state with
  | .pending => if machine.isReaderClosed then closeWriterOnly machine else machine
  | .waitingHeaders =>
    if !machine.isServer then machine.addEvent .needAnswer
    -- The body was closed without a final head, as after only a 1xx: a misuse.
    else if machine.writer.userClosedBody then closeOnBadMessage machine
    else machine
  | .waitingForFlush => if machine.shouldFlush then processBody machine.writeHead else machine
  | .writingBody _ => processBody machine
  | .complete => processCompleteStep machine
  | .closed => machine

/-- A closed writer writes nothing. -/
theorem processWrite_closed (machine : Machine dir) (h : machine.writer.state = .closed) :
    machine.processWrite = machine := by
  simp [processWrite, h]

/-- Returns `true` while the writer is writing a body: its head is written, and it is not over. -/
def isWritingBody (machine : Machine dir) : Bool :=
  machine.writer.state matches .writingBody _

/-- Returns `true` while the reader is in the body of the incoming message. -/
def isReadingBody (machine : Machine dir) : Bool :=
  machine.reader.state matches .readBody _

/--
Returns `true` when the outgoing message needs no more body bytes from the caller: a fixed-length
body holds all of them (its last bytes are written once the caller closes it), or the message is
complete or closed.
-/
def outgoingBodySupplied (machine : Machine dir) : Bool :=
  match machine.writer.state with
  | .writingBody (.fixed n) => machine.writer.userDataBytes == n
  | .complete | .closed => true
  | _ => false

/--
Returns `true` when the peer will not read the rest of the body being written, because the
connection ends after the exchange (`Connection: close`, or the keep-alive quota is used up). Writing
the rest would stall the exchange until a timeout, so the caller should `abandonOutgoingBody`.
-/
def peerWillNotReadBody (machine : Machine dir) : Bool :=
  !machine.keepAlive && machine.isWritingBody

/--
Abandons the body being written, once the peer's answer makes sending it unnecessary: the data not
written yet is dropped and the message completed. When the head announced framing the abandoned body
does not fulfil (bytes still owed under `Content-Length`, or a chunked body without its last chunk),
keep-alive ends: the peer would read the next message as the rest of this body (RFC 9112 §6.3).
-/
def abandonOutgoingBody (machine : Machine dir) : Machine dir :=
  let truncated :=
    match machine.writer.state with
    | .writingBody (.fixed n) => n > 0
    | .writingBody _ => true
    | _ => false
  let machine := machine.modifyWriter fun w =>
    { w with userData := .empty, userDataBytes := 0, userClosedBody := true }
  completeWriterMessage (machine.lowerKeepAlive !truncated)

/--
A server answers a failure with one error response unless a response was already started; a client
stops writing, since the connection cannot carry the exchange any further (RFC 9112 §9.5).
-/
private def answerFailure (machine : Machine dir) : Machine dir :=
  match dir, machine.error with
  | .receiving, some error =>
    if machine.writer.sentMessage then machine
    else (machine.setWriterState .waitingHeaders).sendError (errorResponseStatus error)
  | .receiving, none => machine
  | .sending, error =>
    if error.isSome && !(machine.writer.state matches .closed) then machine.closeWriter.addEvent .close
    else machine

/--
Accounts for `data` read from the body and moves the reader to `next`. `.closeBody` is withheld for
an interim response, whose body is not the exchange's. The chunk is handed out unless the body is
drained internally.
-/
@[inline] private def emitBodyChunk (machine : Machine dir) (next : Reader.State)
    (final incomplete : Bool)
    (extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (data : ByteArray)
    (closeBody : Bool := false) : Machine dir × Option PulledChunk :=
  if !machine.fitsBodyLimit data.size then
    (machine.setFailure .entityTooLarge, none)
  else
    let machine := machine.addBodyBytes data.size |>.setReaderState next
    let machine :=
      if closeBody && !machine.isInterimResponseBody then machine.addEvent .closeBody else machine
    if drainBodyInternally machine then (machine, none)
    else (machine, some { final, incomplete, chunk := { data, extensions } })

/--
Reads one line of the trailer section, `count` fields into it, on its own, so a read that ends
inside the section does not parse the earlier fields again. The empty line ends the body.
-/
private def parseTrailerState (machine : Machine dir)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (count : Nat) :
    Machine dir × Option PulledChunk :=
  -- A server rejects every field forbidden in a request's trailers; a client discards trailers, so
  -- none of them, not even a framing field, can reframe the response.
  let strict := machine.isServer
  let input := machine.reader.input
  -- RFC 9112 §5.2: a user agent replaces an obs-fold in a response with SP. Such a line continues the
  -- previous trailer field, which a client discards with it.
  let folded := !strict && count > 0 && !input.atEnd &&
    (input.curr == ' '.toUInt8 || input.curr == '\t'.toUInt8)
  let (machine, result) :=
    if folded then
      let (machine, part) :=
        parseLine machine .obsFold (parseObsFoldContinuation machine.config) (limit := none)
      (machine, part.map fun _ => some ("", ""))
    else
      parseLine machine .fieldLine (parseTrailerHeader machine.config strict) (limit := none)
  let lineBytes := input.remainingBytes - machine.reader.input.remainingBytes
  -- The section starts afresh for each message.
  let machine := if count == 0 then { machine with reader.trailers := #[] } else machine
  match result with
  | some (some (name, value)) =>
    if !folded && count ≥ machine.config.maxTrailerHeaders then (machine.setFailure .badMessage, none)
    else if !machine.fitsBodyLimit lineBytes then (machine.setFailure .entityTooLarge, none)
    else if folded then (machine.addBodyBytes lineBytes, none)
    else
      let machine :=
        if isForbiddenTrailerField name then machine
        else { machine with reader.trailers := machine.reader.trailers.push (name, value) }
      (machine.addBodyBytes lineBytes |>.setReaderState (.readBody (.trailers ext (count + 1))), none)
  | some none =>
    emitBodyChunk (machine.addBodyBytes lineBytes) .complete true false ext .empty (closeBody := true)
  | none => (machine, none)

/-- Body data needs more input: an error once none will arrive. -/
@[inline] private def bodyNeedsMore (machine : Machine dir) (size : Nat) : Machine dir :=
  if machine.reader.noMoreInput then machine.setFailure .connectionClosed
  else machine.addEvent (.needMoreData (some size))

/-- One transition of body reading, by framing. -/
private def parseBody (machine : Machine dir) : Reader.BodyState → Machine dir × Option PulledChunk
  | .fixed 0 => emitBodyChunk machine .complete true false #[] .empty (closeBody := true)
  | .fixed size =>
    match readFixed machine.reader.input size with
    | .data body rest 0 =>
      emitBodyChunk { machine with reader.input := rest } .complete true false #[] body
        (closeBody := true)
    | .data body rest remaining =>
      emitBodyChunk { machine with reader.input := rest } (.readBody (.fixed remaining)) false false
        #[] body
    | .needMore => (machine.bodyNeedsMore size, none)
    | .invalid => (machine.setFailure .badMessage, none)
  | .chunkedSize =>
    -- The line, like the line break after the data and the trailer section, counts toward
    -- `maxBodySize`, so the wire size of a chunked body stays bounded however small its chunks are.
    let start := machine.reader.input.remainingBytes
    let (machine, result) := parseLine machine .chunkSize (parseChunkSize machine.config)
      (limit := some machine.config.maxChunkLineLength)
      -- A size past 16 significant digits is over `maxChunkSize` too, so it gets the same 413.
      (onHardError := fun | .other "chunk size too large" => .entityTooLarge | _ => .badMessage)
    match result with
    | some (size, ext) =>
      let lineBytes := start - machine.reader.input.remainingBytes
      if size > machine.config.maxChunkSize || !machine.fitsBodyLimit (lineBytes + size) then
        (machine.setFailure .entityTooLarge, none)
      else
        (machine.addBodyBytes lineBytes |>.setReaderState (.readBody (.chunkedBody ext size)), none)
    | none => (machine, none)
  | .chunkedBody ext 0 => parseTrailerState machine ext 0
  | .chunkedBody ext size =>
    match readChunkData machine.reader.input size with
    | .data body rest 0 =>
      emitBodyChunk ({ machine with reader.input := rest }.addBodyBytes 2) (.readBody .chunkedSize)
        false false ext body
    | .data body rest remaining =>
      emitBodyChunk { machine with reader.input := rest } (.readBody (.chunkedBody ext remaining))
        false true ext body
    | .needMore => (machine.bodyNeedsMore size, none)
    | .invalid => (machine.setFailure .badMessage, none)
  | .trailers ext count => parseTrailerState machine ext count
  | .closeDelimited =>
    let input := machine.reader.input
    if !input.atEnd then
      let data := Input.bytes input input.remainingBytes
      emitBodyChunk { machine with reader.input := input.forward input.remainingBytes }
        (.readBody .closeDelimited) false false #[] data
    else if machine.reader.noMoreInput then
      emitBodyChunk machine .complete true false #[] .empty (closeBody := true)
    else
      (machine.addEvent (.needMoreData none), none)

/-! ## Running transitions -/

/--
How far the reader is from having nothing left to do with the input it holds, for `run`: closed
readers rank lowest, and a transition that reads no input moves the reader towards `.closed`.
-/
@[inline] def readerRank : Reader.State → Nat
  | .closed => 0
  | .complete => 1
  | .readBody _ => 2
  | .continue _ => 3
  | .needHeader _ => 4
  | .needStartLine => 5
  | .pending => 6

/--
The progress measure of `run`: the unread input, then the reader's `rank`. Reading a byte lowers it
however the rank changes, since a rank is below 8.
-/
@[inline] def progress (machine : Machine dir) : Nat :=
  8 * machine.reader.input.remainingBytes + readerRank machine.reader.state

/--
Applies the transition `f` while it lowers `progress`, which bounds the number of transitions by the
input the machine holds, with no fuel. Every transition reads input or lowers the reader's rank until
it has nothing left to do. The one that raises the rank without reading input, back to a start line
after an interim response, ends the loop as it should: the final response is read on the next step.
-/
@[specialize] def run (f : Machine dir → Machine dir) (machine : Machine dir) : Machine dir :=
  -- Measured before the transition, so `machine` is not kept alive and `f` updates it in place.
  let before := machine.progress
  let next := f machine
  if _ : next.progress < before then run f next else next
termination_by machine.progress
decreasing_by assumption

/-- A property that holds of the machine and that every transition preserves holds after `run`. -/
theorem run_induction (P : Machine dir → Prop) (f : Machine dir → Machine dir)
    (step : ∀ m, P m → P (f m)) (machine : Machine dir) (h : P machine) : P (run f machine) := by
  rw [run]
  dsimp only
  split
  · exact run_induction P f step (f machine) (step machine h)
  · exact step machine h
termination_by machine.progress
decreasing_by assumption

/-! ## Reading -/

/--
Reads a request line. A line that fails to parse but starts with `HEAD` marks the request as `HEAD`,
so the error response omits its content.
-/
private def processRequestLine (machine : Machine dir) : Machine dir :=
  -- `maxStartLineLength` is checked on the complete line only: on an incomplete line it fires before
  -- the parser's `maxUriLength` check, so the status would depend on where a read ends. The parser's
  -- own limits (leading empty lines, method, `maxUriLength`) bound an incomplete line, and they
  -- leave only the target unbounded, so a line over the limit gets 414 (RFC 9112 §3).
  let input := machine.reader.input
  let headLine := startsWithHead machine.config input
  let failedHead (machine : Machine dir) :=
    if headLine then { machine with request.method := .head } else machine
  let (parsed, result) := parseLine machine .requestLine (parseRequestLineRawVersion machine.config)
    (limit := none) (onHardError := classifyStartLineHardError)
  match result with
  | some (method, uri, version) =>
    let lineBytes := input.remainingBytes - parsed.reader.input.remainingBytes -
      leadingEmptyLineBytes machine.config input
    if lineBytes > machine.config.maxStartLineLength then
      (failedHead machine).setFailure .uriTooLong
    else
      match version with
      | some (v@Version.v11) | some (v@Version.v10) =>
        { parsed with
          request := { method, version := v, uri, headers := .empty }, reader.state := .needHeader 0 }
      | _ => (failedHead parsed).setFailure .unsupportedVersion
  | none => if parsed.failed then failedHead parsed else parsed

/--
Reads a status line. The heads of interim responses count toward `maxHeaderBytes` together with the
final head's fields, so a run of 1xx responses before the final one is bounded.
-/
private def processStatusLine (machine : Machine dir) : Machine dir :=
  let remaining := machine.reader.input.remainingBytes
  let (machine, result) := parseLine machine .statusLine (parseStatusLineRawVersion machine.config)
    (limit := some machine.config.maxStartLineLength)
  match result with
  | some (status, version) =>
    let interimBytes := if status.isInterim then remaining - machine.reader.input.remainingBytes else 0
    let machine :=
      { machine with reader.headerBytesRead := machine.reader.headerBytesRead + interimBytes }
    if machine.reader.headerBytesRead > machine.config.maxHeaderBytes then
      machine.setFailure .headersTooLarge
    else
      -- An HTTP/1.0 response is accepted; `shouldKeepAlive` turns keep-alive off for it.
      match version with
      | some (v@Version.v11) | some (v@Version.v10) =>
        { machine with
          response := { status, version := v, headers := .empty }, reader.state := .needHeader 0 }
      | _ => machine.setFailure .unsupportedVersion
  | none => machine

/--
Reads a start line. At EOF a server's reader closes, also when only the empty lines a server ignores
before a request line are left (RFC 9112 §2.2); a client reads a status line only once its request is
sent, so EOF leaves the exchange without a final response, which is incomplete (RFC 9112 §8).
-/
private def processNeedStartLine (machine : Machine dir) : Machine dir :=
  let reader := machine.reader
  if reader.noMoreInput &&
      (reader.input.atEnd || (machine.isServer && onlyEmptyLinesLeft machine.config reader.input)) then
    if machine.isServer then machine.setReaderState .closed else machine.setFailure .connectionClosed
  else if reader.input.atEnd then machine.addEvent (.needMoreData none)
  else if machine.isServer then processRequestLine machine
  else
    -- Empty lines are discarded as `readIdleInput` discards them, so the verdict does not depend on
    -- whether they arrive before or after the request is written.
    let rest := skipEmptyLines reader.input
    if rest.remainingBytes < reader.input.remainingBytes then { machine with reader.input := rest }
    else if isLoneCR rest then
      if reader.noMoreInput then machine.setFailure .connectionClosed
      else machine.addEvent (.needMoreData none)
    else processStatusLine machine

/-- Adds a field line to the head being read, within the header count and byte limits. -/
private def processParsedHeader (machine : Machine dir) (count : Nat) (lineBytes : Nat)
    (name : Header.Name) (value : Header.Value) : Machine dir :=
  if count ≥ machine.config.maxHeaders then
    machine.setFailure .tooManyHeaders
  else if machine.reader.headerBytesRead + lineBytes > machine.config.maxHeaderBytes then
    machine.setFailure .headersTooLarge
  else
    let machine := { machine with
      reader.headerBytesRead := machine.reader.headerBytesRead + lineBytes
      reader.state := .needHeader (count + 1) }
    if machine.isServer then
      { machine with request.headers := machine.request.headers.insert name value }
    else { machine with response.headers := machine.response.headers.insert name value }

/--
Reads a line that continues the previous field value after an `obs-fold`, which a client replaces
with one SP (RFC 9112 §5.2). A server rejects such a line with 400, as RFC 9112 §5.2 allows: it does
not parse as a field line.
-/
private def processObsFold (machine : Machine dir) : Machine dir :=
  let start := machine.reader.input.remainingBytes
  let (machine, result) := parseLine machine .obsFold (parseObsFoldContinuation machine.config)
    (limit := none) (onHardError := classifyFieldLineHardError)
  match result, machine.response.headers.map.entries.back? with
  | none, _ => machine
  | some _, none => machine.setFailure .badMessage
  | some part, some (name, previous) =>
    let lineBytes := start - machine.reader.input.remainingBytes
    let value :=
      if part.isEmpty then previous.value
      else if previous.value.isEmpty then part
      else previous.value ++ " " ++ part
    if machine.reader.headerBytesRead + lineBytes > machine.config.maxHeaderBytes ||
        value.utf8ByteSize > machine.config.maxHeaderValueLength then
      machine.setFailure .headersTooLarge
    else
      match Header.Value.ofString? value with
      | some value =>
        { machine with
          response.headers := machine.response.headers.replaceLast name value
          reader.headerBytesRead := machine.reader.headerBytesRead + lineBytes }
      | none => machine.setFailure .badMessage

/--
Reads one header line: a field line, the empty line that ends the section (`processHeaders`), or,
on a client, an `obs-fold` continuation.
-/
private def processNeedHeader (machine : Machine dir) (count : Nat) : Machine dir :=
  let input := machine.reader.input
  if !machine.isServer && count > 0 && !input.atEnd &&
      (input.curr == ' '.toUInt8 || input.curr == '\t'.toUInt8) then
    processObsFold machine
  else
    let start := input.remainingBytes
    let (machine, result) := parseLine machine .fieldLine (parseHeaderField machine.config)
      (limit := none) (onHardError := classifyFieldLineHardError)
    match result with
    | some (some (name, value)) =>
      processParsedHeader machine count (start - machine.reader.input.remainingBytes) name value
    | some none => processHeaders machine
    | none => machine

/--
The reader after a whole message: a client goes back to a status line after an interim response,
within the same exchange (RFC 9110 §15.2: it does not count toward `maxMessages`). After
`101 Switching Protocols` or a 2xx to `CONNECT`, the bytes that follow are not HTTP/1.1 and the
connection cannot be reused (RFC 9110 §15.2.2, §9.3.6). Otherwise the reader closes at EOF or when
the connection is not kept alive.
-/
private def processReaderCompleteState (machine : Machine dir) : Machine dir :=
  let reader := machine.reader
  let response := machine.response
  if !machine.isServer && response.status.isInterim then
    { machine with
      reader := { reader with state := .needStartLine, bodyBytesRead := 0 }, response := {} }
  else if !machine.isServer &&
      (response.status.toCode == 101 || startsTunnel machine.request.method response.status) then
    (machine.lowerKeepAlive false).setReaderState .closed
  else if (reader.noMoreInput && reader.input.atEnd) || !machine.keepAlive then
    -- RFC 9112 §9.5: once the final response is in and the connection ends, the rest of the request
    -- body would not be read.
    let machine :=
      if !machine.isServer && !machine.keepAlive && machine.isWritingBody then
        machine.abandonOutgoingBody
      else machine
    machine.setReaderState .closed
  else
    machine

/--
One transition of the reader, chosen by its state. The machine drains a body itself when no caller
reads it: the body of an interim response, a request body after the response, and an empty response
body (204, 304, HEAD), which has nothing to hand out.
-/
private def readStep (machine : Machine dir) : Machine dir :=
  match machine.reader.state with
  | .pending =>
    if machine.writer.state matches .closed then machine.setReaderState .closed
    else if !machine.isServer && machine.writer.state matches .waitingForFlush then
      -- A head this step writes is on the wire before any response to it.
      if machine.shouldFlush then machine.setReaderState .needStartLine
      -- The peer closed before the held head was written, so no response can come.
      else if machine.reader.noMoreInput && machine.reader.input.atEnd then
        machine.setFailure .connectionClosed
      else readIdleInput machine
    else readIdleInput machine
  | .needStartLine => processNeedStartLine machine
  | .needHeader count => processNeedHeader machine count
  | .readBody body =>
    if drainBodyInternally machine || (!machine.isServer && body matches .fixed 0) then
      (parseBody machine body).1
    else machine
  | .continue _ => machine
  | .complete => processReaderCompleteState machine
  | .closed => machine

/--
Reads the input the machine holds as far as it goes: start lines, field lines, and the bodies the
machine drains itself.
-/
def processRead (machine : Machine dir) : Machine dir :=
  match machine.reader.state with
  -- `.pending` too: a client's request head going out moves it to a status line without reading.
  | .pending | .needStartLine | .needHeader _ | .readBody _ => run readStep machine
  -- The other states take at most one transition, so they skip the loop.
  | _ => readStep machine

/-- A closed reader reads nothing. -/
theorem processRead_closed (machine : Machine dir) (h : machine.reader.state = .closed) :
    machine.processRead = machine := by
  rw [processRead, run]
  simp [readStep, h]

/-- Executes one step of the machine: reads, answers a failure, writes, and takes events and output. -/
def step (machine : Machine dir) : Machine dir × StepResult dir :=
  -- A failure closes the reader, and `processWrite` closes a pending writer once the reader is
  -- closed, so the error response is queued before writing.
  let machine := machine.processRead.answerFailure.processWrite
  let (machine, events) := machine.takeEvents
  let (machine, output) := machine.takeOutput
  (machine, { events, output })

/-- Parses the body until it produces a chunk or makes no progress, under the bound of `run`. -/
private def pullNextChunk (machine : Machine dir) : Machine dir × Option PulledChunk :=
  match machine.reader.state with
  | .readBody body =>
    let before := machine.progress
    let (next, pulled) := parseBody machine body
    if pulled.isNone then
      if _ : next.progress < before then pullNextChunk next else (next, none)
    else
      (next, pulled)
  | _ => (machine, none)
termination_by machine.progress
decreasing_by assumption

/-- Pulls at most one body chunk: parses the body until it produces a chunk or cannot continue. -/
@[inline] def pullBody (machine : Machine dir) : Machine dir × Option PulledChunk :=
  let (machine, pulled) := pullNextChunk machine
  ({ machine with pullBodyStalled := pulled.isNone && machine.canPullBody }, pulled)

/--
Pulls and drops body chunks until the reader is blocked, for a caller that will not read the body
but needs the connection to move on: while chunks stay buffered, the next message is not parsed.
-/
def drainBody (machine : Machine dir) : Machine dir :=
  run (fun machine => if machine.canPullBodyNow then machine.pullBody.fst else machine) machine

end Std.Http.Protocol.H1.Machine
