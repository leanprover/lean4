/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.Array
public import Std.Http.Protocol.H1.Basic
public import Std.Http.Protocol.H1.Config
public import Std.Http.Protocol.H1.Head
public import Std.Http.Protocol.H1.Message
public import Std.Http.Protocol.H1.Parser
public import Std.Http.Protocol.H1.Reader
public import Std.Http.Protocol.H1.Writer
public import Std.Http.Protocol.H1.Redirect

public section

/-!
# HTTP/1.1 protocol machine

A machine for one side of an HTTP/1.1 connection, without I/O. The caller feeds it the bytes it
receives (`feed`), gives it the messages to send (`send`, `sendData`), and runs `step`, which
returns events and the bytes to write. Body data received is pulled with `pullBody`.
`Direction.receiving` is a server, `Direction.sending` a client.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std Std.Internal Http.Internal Parsec ByteArray

/--
The HTTP/1.1 protocol machine.
-/
structure Machine (dir : Direction) where
  /--
  The side that reads incoming messages.
  -/
  reader : Reader dir := {}

  /--
  The side that writes outgoing messages.
  -/
  writer : Writer dir := {}

  /--
  Limits and options.
  -/
  config : Config

  /--
  Events not yet returned by `step`.
  -/
  events : Array (Event dir) := #[]

  /--
  Why the machine failed or closed the connection, if it did.
  -/
  error : Option Error := none

  /--
  The `Date` field value a server writes in each final response whose head has none, including the
  error responses the machine writes itself (RFC 9110 §6.6.1). The caller keeps it current; with
  `none`, no `Date` is added.
  -/
  date : Option Header.Value := none

  /--
  Whether the connection stays open after the current exchange. It never turns back on.
  -/
  keepAlive : Bool := config.enableKeepAlive

namespace Machine

@[inline]
private def modifyWriter (machine : Machine dir) (fn : Writer dir → Writer dir) : Machine dir :=
  { machine with writer := fn machine.writer }

@[inline]
private def modifyReader (machine : Machine dir) (fn : Reader dir → Reader dir) : Machine dir :=
  { machine with reader := fn machine.reader }

@[inline]
private def setReaderState (machine : Machine dir) (state : Reader.State) : Machine dir :=
  machine.modifyReader ({ · with state })

@[inline]
private def setWriterState (machine : Machine dir) (state : Writer.State) : Machine dir :=
  machine.modifyWriter ({ · with state })

@[inline]
private def addEvent (machine : Machine dir) (event : Event dir) : Machine dir :=
  { machine with events := machine.events.push event }

@[inline]
private def disableKeepAlive (machine : Machine dir) : Machine dir :=
  { machine with keepAlive := false }

/--
Fails the machine with `error`: records it, reports it as an event and closes the reader. The
message's framing is lost, so the connection is not reused (RFC 9112 §6.3 rule 5, §8). A server
answers the failure in the same `step` (`answerFailure`).
-/
@[inline]
private def setFailure (machine : Machine dir) (error : H1.Error) : Machine dir :=
  { machine with
    events := machine.events.push (.failed error)
    reader := { machine.reader with state := .closed }
    error := some error
    keepAlive := false }

/--
Applies the keep-alive limits of an exchange with a message head `head`: `maxMessages`, and what
`head`'s `Connection` field says.
-/
@[inline]
private def limitKeepAlive (machine : Machine dir) (head : Message.Head d) : Machine dir :=
  { machine with
    keepAlive := machine.keepAlive &&
      machine.reader.messageCount + 1 < machine.config.maxMessages && head.shouldKeepAlive }

/--
Whether the machine reads the body itself instead of leaving it to `pullBody`. A server drains the
rest of a request body once its response is fully written: until then the handler may still read it,
for example to stream it back. An empty remainder has nothing to deliver, so it is read as soon as
the response head is given, and an empty response body as soon as it starts, since it has no bytes
to expose and would otherwise stall the connection (204, 304, HEAD responses).
-/
@[inline]
private def readsBodyItself (machine : Machine dir) : Bool :=
  let emptyRest := machine.reader.state matches .readBody (.fixed 0)
  match dir with
  | .receiving =>
    (machine.writer.state matches .complete | .closed) || (machine.writer.sentMessage && emptyRest)
  | .sending => emptyRest

/--
Whether the machine failed. `error` holds the cause.
-/
@[inline]
def failed (machine : Machine dir) : Bool :=
  machine.error.isSome

/--
Whether the reader read the whole current message.
-/
@[inline]
def isReaderComplete (machine : Machine dir) : Bool :=
  machine.reader.state matches .complete

/--
Whether the reader is closed.
-/
@[inline]
def isReaderClosed (machine : Machine dir) : Bool :=
  machine.reader.state matches .closed

/--
Whether a request waits for a `canContinue` decision.
-/
@[inline]
def isReaderAwaitingContinue (machine : Machine dir) : Bool :=
  machine.reader.state matches .«continue» _

/--
Whether the head given to `send` can be written: its body's framing is known, or the exchange is
over. Body data counts, so a streamed body starts going out before it ends, except in an HTTP/1.0
request: it cannot be chunked (RFC 9112 §6.1), so unless its length was set it waits for its whole
body.
-/
@[inline]
private def shouldFlush (machine : Machine dir) : Bool :=
  machine.failed ∨
  machine.reader.state == .closed ∨
  machine.writer.noMoreUserData ∨
  machine.writer.knownSize.isSome ∨
  (machine.writer.userData.size > 0 ∧
    ¬((dir matches .sending) && machine.writer.messageHead.version == .v10))

/--
Whether the machine waits for the head of the message to send (`send`).
-/
@[inline]
def isWaitingMessage (machine : Machine dir) : Bool :=
  machine.writer.state == .waitingHeaders

/--
Whether both sides are closed and all output was taken.
-/
@[inline]
def halted (machine : Machine dir) : Bool :=
  machine.reader.state matches .closed && machine.writer.state matches .closed &&
    machine.writer.outputData.isEmpty

/--
Whether the body being read is for the caller to pull (`pullBody`).
-/
@[inline]
def canPullBody (machine : Machine dir) : Bool :=
  !machine.readsBodyItself && machine.reader.state matches .readBody _

/--
How many more bytes the reader needs to finish the body bytes it reads: the rest of a fixed-length
body or of a chunk's data. `none` when it does not know.
-/
def bodyBytesWanted (machine : Machine dir) : Option Nat :=
  match machine.reader.state with
  | .readBody (.fixed n) | .readBody (.chunkedBody _ n) => if n = 0 then none else some n
  | _ => none

/--
The length of the body being read as its framing states it, while none of it was read: `fixed n` or
`chunked`. `none` in any other state.
-/
def bodyLength? (machine : Machine dir) : Option Body.Length :=
  match machine.reader.state with
  | .readBody (.fixed n) => some (.fixed n)
  | .readBody .chunkedSize => some .chunked
  | _ => none

/--
Whether the peer may still be sending when the connection ends: it has not closed its side, and a
message is unfinished, the reader stopped reading, or the machine still took input when it stopped,
after failing or with input it never read. Input that arrives after the reader stopped, such as a
pipelined request (a server does not read while a handler runs) or a tunnel's bytes, waits unread.
Closing a connection with unread input resets it, which can destroy the last response before the
peer reads it (RFC 9112 §9.6).
-/
def peerMayStillSend (machine : Machine dir) : Bool :=
  let reader := machine.reader
  !reader.peerClosed &&
    (reader.inMessage || reader.isClosed ||
      (!reader.inputStopped && (machine.failed || reader.remainingBytes > 0)))

/--
Starts the next exchange on a connection that stays open, keeping the unread input and the output
not yet taken.
-/
private def resetForNextMessage (machine : Machine dir) : Machine dir :=
  { machine with
    reader := { input := machine.reader.input, peerClosed := machine.reader.peerClosed,
                inputStopped := machine.reader.inputStopped,
                messageCount := machine.reader.messageCount + 1 }
    writer := { outputData := machine.writer.outputData }
    events := machine.events.push .next
    error := none }

/--
Ends the header section and starts reading the body as `body`. The head is reported; a server then
waits for the response, and first for a `canContinue` decision when the request expects one. An
interim (1xx) response has no body, so a client reads the response that follows it, in the same
exchange; it does not count toward `maxMessages` (RFC 9110 §15.2).
-/
private def startBody (machine : Machine dir) (body : Reader.BodyState) : Machine dir :=
  let head := machine.reader.messageHead
  let machine := { machine with reader := { machine.reader with inMessage := true } }
  let machine := machine.addEvent (.endHeaders head)
  match dir, machine, head with
  | .receiving, machine, head =>
    let machine :=
      if expectsContinue head then
        machine.addEvent .«continue» |>.setReaderState (.«continue» body)
      else
        machine.setReaderState (.readBody body)
    machine.setWriterState .waitingHeaders |>.addEvent .needAnswer
  | .sending, machine, head =>
    if head.status.isInterim then
      -- The interim head's bytes stay counted toward `maxHeaderBytes`.
      machine.modifyReader fun reader =>
        { reader with
          state := .needStartLine, bodyBytesRead := 0, inMessage := false, messageHead := ∅ }
    else machine.setReaderState (.readBody body)

/--
Ends the header section: applies the keep-alive limits, checks the head and chooses how to read its
body, and starts it. A body that ends with the connection turns keep-alive off.
-/
private def processHeaders (machine : Machine dir) : Machine dir :=
  let machine := machine.limitKeepAlive machine.reader.messageHead
  let body :=
    match dir, machine with
    | .receiving, machine => checkRequestHead machine.config machine.reader.messageHead
    | .sending, machine =>
      checkResponseHead machine.writer.messageHead.method machine.reader.messageHead
  match body with
  | .error err => machine.setFailure err
  | .ok (.fixed n) =>
    if n > machine.config.maxBodySize then machine.setFailure .entityTooLarge
    else machine.startBody (.fixed n)
  | .ok .closeDelimited => machine.disableKeepAlive.startBody .closeDelimited
  | .ok body => machine.startBody body

/--
What a server's response may carry: what its status allows, or nothing when it starts a tunnel
(`startsTunnel`).
-/
@[inline]
private def responseRule (requestMethod : Method) (status : Status) : ContentRule :=
  if startsTunnel requestMethod status then .none else status.contentRule

/--
Whether the outgoing message is a response that carries no body: one to a `HEAD` request, one whose
status forbids content, or a tunnel's head.
-/
@[inline]
private def omitsResponseBody (machine : Machine dir) (message : Message.Head dir.swap) : Bool :=
  match dir with
  | .receiving =>
    responseRule machine.reader.messageHead.method message.status != .any ∨
      machine.reader.messageHead.method == .head
  | .sending => false

/--
Writes the head of the outgoing message and enters the state that writes its body, or completes the
message when its body is omitted (`omitsResponseBody`). A final response written while an
`Expect: 100-continue` decision is pending ends the exchange without the body
(`processCompleteStep`), so its head says `close` (RFC 9110 §10.1.1).
-/
private def writeHead (messageHead : Message.Head dir.swap) (machine : Machine dir) : Machine dir :=
  let omits := omitsResponseBody machine messageHead
  let machine := machine.limitKeepAlive messageHead
  let machine := if machine.isReaderAwaitingContinue then machine.disableKeepAlive else machine
  let size : Body.Length :=
    match machine.writer.knownSize with
    | some size => size
    | none =>
      if machine.writer.userClosedBody then .fixed machine.writer.userDataBytes else .chunked
  -- RFC 9110 §15.3.6: a 205 response is framed as empty, whatever length was set for its body.
  let size : Body.Length :=
    match dir, messageHead with
    | .receiving, messageHead => if messageHead.status.contentRule == .empty then .fixed 0 else size
    | .sending, _ => size
  -- HTTP/1.0 has no chunked coding: a response of unknown length ends when the connection closes,
  -- unless its body is omitted (a HEAD response), which leaves nothing to delimit.
  let version := machine.reader.messageHead.version
  let closeDelimited := (dir matches .receiving) && version == .v10 && size == .chunked
  let machine := if closeDelimited && !omits then machine.disableKeepAlive else machine
  let state : Writer.State :=
    if omits then .complete
    else
      match size with
      | .fixed n => .writingBodyFixed n
      | .chunked => .writingBodyOpen !closeDelimited
  -- Matching on `dir` below generalizes `machine`, so everything needed from it is read here.
  let keepAlive := machine.keepAlive
  let date := machine.date
  let agentName := machine.config.agentName
  let head : ByteArray :=
    match dir, machine, messageHead with
    | .receiving, machine, messageHead =>
      encodeResponseHead messageHead version keepAlive date agentName size
        (rule := responseRule machine.reader.messageHead.method messageHead.status)
    | .sending, _, messageHead => encodeRequestHead messageHead keepAlive agentName size
  machine.modifyWriter fun writer =>
    { writer with outputData := writer.outputData.push head, state }

/--
Feeds input bytes into the reader side of the machine.
-/
@[inline]
def feed (machine : Machine dir) (data : ByteArray) : Machine dir :=
  if machine.reader.isClosed ∨ machine.failed then
    machine
  else
    let reader := machine.reader.feed data
    let machine := { machine with reader }
    let config := machine.config
    -- Bounds buffered body bytes and parser lookahead, so that a stalled consumer cannot make the
    -- machine hold unbounded input.
    if reader.remainingBytes >
        config.maxBodySize + config.maxHeaderBytes + config.maxStartLineLength +
          config.maxChunkLineLength then
      machine.setFailure .entityTooLarge
    else
      machine

/--
Stops taking input without changing the reader state: input already buffered is still read, then the
reader ends as at the end of input.
-/
@[inline]
private def stopInput (machine : Machine dir) : Machine dir :=
  { machine with reader := { machine.reader with inputStopped := true } }

/--
Stops reading: no more input is read, and the connection does not stay open.
-/
@[inline]
private def stopReading (machine : Machine dir) : Machine dir :=
  { machine with
    keepAlive := false
    reader := { machine.reader with inputStopped := true, state := .closed } }

/--
Closes the writer side, preventing any further message output.
-/
@[inline]
def closeWriter (machine : Machine dir) : Machine dir :=
  machine.setWriterState .closed

/--
Signals that the user is not sending data anymore.
-/
@[inline]
def userClosedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userClosedBody := true })

/--
Signals that the peer closed its side of the connection, so no more input will arrive.
-/
@[inline]
def noMoreInput (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with peerClosed := true })

/--
Set a known size for the message body, replacing any previous value. Once the machine has failed it
is ignored, so an error response the machine sends in place of the caller's keeps the length of its
own content.
-/
@[inline]
def setKnownSize (machine : Machine dir) (size : Body.Length) : Machine dir :=
  if machine.error.isSome then machine
  else machine.modifyWriter (fun w => { w with knownSize := some size })

/--
Reconciles the body length the caller set (`knownSize`) with the framing fields of the message head
passed to `send`. The fields' length is adopted when none was set, or when only `chunked` was, which
leaves the length unknown (a `Body.stream` starts that way). Returns `none` when the two contradict,
or when the fields describe no length.
-/
private def reconcileOutgoingFraming (machine : Machine dir)
    (headerSize : Option Body.Length) (framingInHeaders : Bool) : Option (Machine dir) :=
  match headerSize with
  -- The fixed-length writer closes the connection if the body then runs over or falls short.
  | some parsed =>
    if machine.writer.knownSize.all (fun known => known == .chunked || known == parsed) then
      some (machine.setKnownSize parsed)
    else none
  | none => if framingInHeaders then none else some machine

/--
Leaves the body of a response without content (`omitsResponseBody`) off the wire, dropping any body
data given. Its head states no length when its status allows no framing fields (1xx, 204, a tunnel),
the length set for a 205 or a 304, and for a response to `HEAD` the length a GET would have: chunked
framing when that is not known, not the `Content-Length: 0` of a body closed empty (RFC 9110
§9.3.2).
-/
private def omitResponseBody (machine : Machine .receiving) (status : Status) :
    Machine .receiving :=
  let knownSize := match responseRule machine.reader.messageHead.method status with
    | .none => some (.fixed 0)
    | .any => some (machine.writer.knownSize.getD .chunked)
    | .empty | .notModified => machine.writer.knownSize
  machine.modifyWriter fun w =>
    { w with userClosedBody := true, knownSize, userData := #[], userDataBytes := 0 }

/--
Takes `message` as the head of the final message to send, written once its framing is known
(`shouldFlush`). The body of a response without content (`omits`) is left off the wire.
-/
private def acceptFinal (machine : Machine dir) (message : Message.Head dir.swap) (omits : Bool) :
    Machine dir :=
  let machine := machine.modifyWriter ({ · with messageHead := message, state := .waitingForFlush })
  match dir, machine, message with
  | .sending, machine, _ => machine.setReaderState .needStartLine
  | .receiving, machine, message =>
    let machine := if omits then machine.omitResponseBody message.status else machine
    -- What follows a 101 or a tunnel's head is not HTTP, and this server speaks neither.
    if leavesHttp machine.reader.messageHead.method message.status then machine.stopReading
    else machine

/--
Sends a response the machine writes itself (`errorResponse`) with `text/plain` content, which
RFC 9110 §15.5 and §15.6 ask of 4xx and 5xx responses, in place of any body data given. A response
to `HEAD` omits the content and keeps its `Content-Length`. Does nothing once a response is under
way, whose length and body it would otherwise replace.
-/
private def sendError (machine : Machine .receiving) (status : Status) : Machine .receiving :=
  if machine.writer.sentMessage then
    machine
  else
    let (head, content) := errorResponse status
    let machine := machine.modifyWriter ({ · with
      knownSize := some (.fixed content.size), userData := #[{ data := content }]
      userDataBytes := content.size, userClosedBody := true })
    acceptFinal machine head (omitsResponseBody machine head)

/--
Handles a message head that `reconcileOutgoingFraming` rejected. None of that message is written:
a server answers `500 Internal Server Error` with a short `text/plain` explanation and closes the
connection, and a client ends the exchange. Both report the mismatch as a failure, a mistake of the
sender's own code that a server passes to `Handler.onFailure`, and the machine halts once its output
is taken.
-/
private def rejectOutgoingFraming (machine : Machine dir) : Machine dir :=
  let machine :=
    machine.setFailure (.other "Content-Length or Transfer-Encoding contradicts the body")
      |>.stopInput
  match dir, machine with
  | .receiving, machine => machine.sendError .internalServerError
  | .sending, machine => machine.closeWriter

/--
Writes an informational (1xx) response at once. It has no content, so framing fields the caller set
are left out (RFC 9110 §15.2), and a server never sends one to an HTTP/1.0 client. Like a final
response it says HTTP/1.1 (RFC 9110 §6.2), and its `Connection` field limits keep-alive as a final
head's does: a server that sends `close` processes no further requests (RFC 9112 §9.6).
-/
private def sendInterim (machine : Machine .receiving) (head : Response.Head) :
    Machine .receiving :=
  let head : Response.Head := { head with
    version := .v11
    headers := head.headers
      |>.erase Header.Name.contentLength
      |>.erase Header.Name.transferEncoding }
  machine.limitKeepAlive (d := .sending) head |>.modifyWriter fun w =>
    { w with outputData := w.outputData.push (ByteArray.empty ++ head) }

/--
Whether the outgoing message cannot be framed for HTTP/1.0, which has no transfer coding (RFC 9112
§6.1): a response to an HTTP/1.0 request whose `Transfer-Encoding` lists a coding other than
`chunked`, whose content would go out still coded, or an HTTP/1.0 request whose length was set as
`chunked`.
-/
private def unframeableForHttp10 (machine : Machine dir) (message : Message.Head dir.swap) : Bool :=
  match dir with
  | .receiving =>
    machine.reader.messageHead.version == .v10 &&
      match message.headers.getAll? Header.Name.transferEncoding with
      | some values =>
        (Header.TransferEncoding.parseFieldLines? values).any (·.any (· != "chunked"))
      | none => false
  | .sending => message.version == .v10 && machine.writer.knownSize == some .chunked

/--
Gives the machine the head of the message to send. Does nothing unless the machine waits for one
(`isWaitingMessage`).

An informational (1xx) response is written at once (`sendInterim`), and the machine goes on waiting
for the final response. The reader is not affected: `canContinue` resolves an `Expect: 100-continue`
decision. No 1xx goes to an HTTP/1.0 client (RFC 9110 §15.2). `101 Switching Protocols` ends the
exchange instead, without content or framing fields, and the connection then closes: what follows is
not HTTP (RFC 9110 §15.2.2).

A `Content-Length` in the head gives the length of a body set as `chunked`, whose length is unknown.
A head whose `Content-Length` or `Transfer-Encoding` otherwise contradicts the length set with
`setKnownSize`, or describes no length, is not written, and neither is a message HTTP/1.0 cannot
frame (`unframeableForHttp10`): a server answers `500 Internal Server Error` and closes the
connection, and a client ends the exchange (`rejectOutgoingFraming`).

A response without content (`omitsResponseBody`) cannot contradict its length, and a HEAD response
advertises the `Content-Length` of its head. A 2xx to `CONNECT` is written without content or
framing fields, and the connection then closes.
-/
def send (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  if !machine.isWaitingMessage then
    machine
  else
    match dir, machine, message with
    | .receiving, machine, message =>
      if message.status.isInformational && machine.reader.messageHead.version != .v11 then
        machine
      else if message.status.isInterim then
        machine.sendInterim message
      else
        sendFinal machine message
    | .sending, machine, message => sendFinal machine message
where
  sendFinal {dir} (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
    let omits := omitsResponseBody machine message
    let framingInHeaders := message.hasFramingFields
    let headerSize := if framingInHeaders then message.getSize false else none
    let reconciled :=
      -- RFC 9110 §8.6: the `Content-Length` of a response without content is the length a GET would
      -- have, which only the caller knows.
      if omits then some (headerSize.elim machine machine.setKnownSize)
      else reconcileOutgoingFraming machine headerSize framingInHeaders
    match reconciled.filter (fun machine => omits || !unframeableForHttp10 machine message) with
    | none => rejectOutgoingFraming machine
    | some machine => acceptFinal machine message omits

/--
Enqueues body chunks into the writer buffer for encoding and sending. Once the body was closed
(`userClosedBody`, or a body that is omitted) or the message is over, the chunks are dropped.
-/
@[inline]
def sendData (machine : Machine dir) (data : Array Chunk) : Machine dir :=
  if data.isEmpty || machine.writer.noMoreUserData then
    machine
  else
    machine.modifyWriter (fun writer =>
      let extraBytes := data.foldl (fun acc c => acc + c.data.size) 0
      { writer with
        userData := writer.userData ++ data
        userDataBytes := writer.userDataBytes + extraBytes })

/--
Resolves an `Expect: 100-continue` decision.

When `status` is `100 Continue`, sends the interim response and advances to body
reading. For any other status, sends the rejection response (typically 417) with a short
`text/plain` explanation, unless a final response was already sent, disables keep-alive, and closes
the reader — the body will not be received.
-/
def canContinue (machine : Machine dir) (status : Status) : Machine dir :=
  match dir, machine.reader.state with
  | .sending, _ => machine
  | .receiving, .«continue» body =>
    if status == .«continue» then
      machine.sendInterim { status := .«continue» } |>.setReaderState (.readBody body)
    else
      machine.sendError status |>.stopReading
  | .receiving, _ => machine

/--
Ends the connection with an error: answers `status` with `Connection: close` and a short
`text/plain` explanation if no response was started, and otherwise stops writing the one under way.
No more input is read.
-/
def closeWithError (machine : Machine .receiving) (status : Status) : Machine .receiving :=
  -- With keep-alive on, a reader that finished its request would wait for the next one whenever
  -- unread input follows it, and the machine would never halt.
  let machine := machine.disableKeepAlive.stopInput
  if machine.isWaitingMessage then machine.sendError status else machine.closeWriter

/--
Takes and clears all accumulated events, returning the drained array.
-/
@[inline]
def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/--
Ends the connection after a mistake of the sender's own code, such as a body longer or shorter than
its stated length: nothing more is read or written. The message on the wire is cut short, so a
server reports it to `Handler.onFailure`.
-/
@[inline]
private def closeOnBadMessage (machine : Machine dir) : Machine dir :=
  machine.setFailure .badMessage |>.stopInput |>.closeWriter |>.addEvent .close

/--
Stops writing messages and reports that the connection ends.
-/
@[inline]
private def endWrites (machine : Machine dir) : Machine dir :=
  machine.setWriterState .closed |>.addEvent .close

/--
After a message was written: the next exchange starts if the reader finished its message and the
connection stays open. The connection ends if the reader is closed, if a request waits for a
`canContinue` decision whose body will now never come, or if keep-alive is off. Otherwise the writer
waits for the reader.
-/
private def processCompleteStep (machine : Machine dir) : Machine dir :=
  match dir, machine.reader.state with
  | _, .complete => if machine.keepAlive then resetForNextMessage machine else endWrites machine
  | _, .closed => endWrites machine
  | .receiving, .continue _ => endWrites machine.stopReading
  | _, _ => if machine.keepAlive then machine else endWrites machine

/--
Writes a body of stated length, `n` bytes of which are left. A body that runs over or ends short of
the length ends the connection, since the peer would read the next message from the wrong place. The
last bytes are held back until the body is closed, so that a late extra chunk is still caught.
-/
private def processFixedBody (machine : Machine dir) (n : Nat) : Machine dir :=
  let writer := machine.writer
  if writer.userDataBytes > n || (n = 0 && writer.userData.size > 0) then
    closeOnBadMessage machine
  else if !writer.userClosedBody then
    if writer.userData.isEmpty || writer.userDataBytes = n then machine
    else
      let state : Writer.State := .writingBodyFixed (n - writer.userDataBytes)
      { machine with writer := { writer.writeBody false with state } }
  else
    let machine := { machine with writer := writer.writeBody false }
    if writer.userDataBytes < n then closeOnBadMessage machine else machine.setWriterState .complete

/--
Writes a chunked body, or the body of an HTTP/1.0 response that ends when the connection closes.
-/
private def processOpenEndedBody (machine : Machine dir) (chunked : Bool) : Machine dir :=
  if machine.writer.userClosedBody then
    machine.modifyWriter fun writer =>
      let writer := writer.writeBody chunked
      let outputData :=
        if chunked then writer.outputData.push "0\r\n\r\n".toUTF8 else writer.outputData
      { writer with outputData, state := .complete }
  else if machine.writer.userData.size > 0 then
    machine.modifyWriter (·.writeBody chunked)
  else
    machine

/--
Advances the writer. A server's pending writer closes with the reader, and a writer waiting for a
head asks a client for one (`.needAnswer`). Once a head was given, the writer goes through three
stages in one call: it writes the head when its framing is known (`shouldFlush`), then the body data
given, and once the message is complete it moves on (`processCompleteStep`).
-/
private def processWrite (machine : Machine dir) : Machine dir :=
  match machine.writer.state with
  | .pending =>
    if machine.reader.isClosed then machine.closeWriter else machine
  | .waitingHeaders =>
    match dir with
    | .receiving =>
      -- Misuse: the body was closed without a final response, as after only a 1xx interim `send`.
      if machine.writer.userClosedBody then closeOnBadMessage machine else machine
    | .sending => machine.addEvent .needAnswer
  | .waitingForFlush | .writingBodyFixed _ | .writingBodyOpen _ | .complete =>
    let machine :=
      if machine.writer.state matches .waitingForFlush && machine.shouldFlush then
        machine.writeHead machine.writer.messageHead
      else
        machine
    let machine :=
      match machine.writer.state with
      | .writingBodyFixed n => processFixedBody machine n
      | .writingBodyOpen chunked => processOpenEndedBody machine chunked
      | _ => machine
    if machine.writer.state matches .complete then processCompleteStep machine else machine
  | .closed =>
    machine

/--
A server answers a failure with one error response, with a short `text/plain` explanation, unless a
response was already started. The response it gives makes `sentMessage` hold, so later steps do
nothing. A client that failed writes nothing more: a request head not yet written never goes out, so
a request that failed before it was sent cannot reach the server (or run twice on a retry), and a
body in progress stops.
-/
private def answerFailure (machine : Machine dir) : Machine dir :=
  match dir, machine.error with
  | .receiving, some error => machine.sendError error.responseStatus
  | .sending, some _ => if machine.writer.state matches .closed then machine else machine.endWrites
  | _, none => machine

/-!
### Reading

The reader advances one transition at a time (`readStep`), and `processRead` runs transitions until
one of them waits: for input, for a caller's decision, or for the next `step`. Only start and header
lines go on, and each consumes input (`readStep_decreases`). A body the machine reads itself is read
in one transition (`pullLoop`), whose body transitions go on only while they consume input
(`bodyStep_decreases`). The proofs need nothing about the parsers, which are `partial`: `parseThen`
fails an item that consumed no input.

The reader transitions are inlined into `processRead`, so the pairs they return and the parser
closures are not allocated. Body transitions go through `bodyStep`, once per chunk.
-/

/--
The scan to keep when the parser need not run again on the unread input: its last attempt ran out of
input after `tried` bytes, more input may come, the line is still below `limit`, and the bytes that
arrived since continue the line's run (`LineScan.extend`). `none` when the parser has to run.
-/
@[inline]
private def resumeScan (reader : Reader dir) (kind : LineKind) (config : Config)
    (limit : Option Nat) : Option LineScan :=
  let input := reader.input
  if reader.tried != 0 && reader.tried ≤ input.remainingBytes && !reader.noMoreInput &&
      limit.all (input.remainingBytes < ·) then
    reader.scan.extend kind config input.array (input.pos + reader.tried) input.array.size
  else
    none

/--
The failure a line parser's error stands for: a target, field name or field value over its limit is
too large, as too many fields are (RFC 6585 §5 answers both with 431), and so is a chunk size past
16 significant digits, which is over `maxChunkSize` too. A method the server does not recognize is
not implemented, and anything else is malformed.
-/
private def lineError : Std.Internal.Parsec.Error → H1.Error
  | .other "uri too long" => .uriTooLong
  | .other "unrecognized method" => .unsupportedMethod
  | .other "header name too long" | .other "header value too long" => .headersTooLarge
  | .other "chunk size too large" => .entityTooLarge
  | _ => .badMessage

/--
Runs `parser` on the unread input. On success it continues with `next`, given the machine with the
input advanced past the item, the parsed value, and the item's length in bytes. Otherwise the reader
stops with `stop`. When the input ends inside the item, it asks for more, unless no more input will
come (`connectionClosed`) or the item has already reached `limit` bytes (`badMessage`). Malformed
bytes fail with `onError` (`lineError`), and a complete item longer than `limit` fails with
`badMessage`.

The item is a line of kind `kind`. After an incomplete attempt the parser runs again only when the
bytes that arrived since may do more than continue the line (`resumeScan`). A byte that cannot
continue it therefore fails it at once, as it would if the line had arrived in one read, while a line
that arrives in pieces is parsed a bounded number of times.
-/
@[inline]
private def parseThen (machine : Machine dir) (kind : LineKind) (parser : Parser α) (stop : β)
    (next : Machine dir → α → Nat → Machine dir × β) (limit : Option Nat := none)
    (onError : Std.Internal.Parsec.Error → H1.Error := lineError) : Machine dir × β :=
  let input := machine.reader.input
  match resumeScan machine.reader kind machine.config limit with
  | some scan =>
    let machine := machine.modifyReader ({ · with tried := input.remainingBytes, scan })
    (machine.addEvent (.needMoreData none), stop)
  | none =>
    match parser input with
    | .success rest result =>
      let length := input.remainingBytes - rest.remainingBytes
      -- The parsers are `partial`, so only this check shows that an item consumes input.
      if length == 0 || limit.any (length > ·) then
        (machine.setFailure .badMessage, stop)
      else
        next (machine.modifyReader (·.setInput rest)) result length
    | .error rest .eof =>
      if machine.reader.noMoreInput then
        (machine.setFailure .connectionClosed, stop)
      else if limit.any (input.remainingBytes - rest.remainingBytes ≥ ·) then
        (machine.setFailure .badMessage, stop)
      else
        let scan := LineScan.classify kind machine.config input.array input.pos input.array.size
        let machine := machine.modifyReader ({ · with tried := input.remainingBytes, scan })
        (machine.addEvent (.needMoreData none), stop)
    | .error _ err =>
      (machine.setFailure (onError err), stop)

/--
Whether the unread input starts with a space or a tab, as an obs-fold line does.
-/
@[inline]
private def startsWithWhitespace (input : ByteArray.Iterator) : Bool :=
  input.array[input.pos]?.any (LineScan.Class.ows.accepts ·)

/-! #### Body -/

/--
What one body transition produced.
-/
private inductive BodyStep where
  /--
  The reader waits for input, or failed.
  -/
  | stop

  /--
  The reader moved on without data for the caller: it read a chunk-size line or a trailer field, or
  drained body bytes itself.
  -/
  | next

  /--
  Body data for the caller.
  -/
  | chunk (pulled : PulledChunk)

/--
Waits for more of a body item of which `expect` bytes are missing, or fails if no more input will
come.
-/
@[inline]
private def waitForBody (machine : Machine dir) (expect : Option Nat) : Machine dir × BodyStep :=
  if machine.reader.noMoreInput then
    (machine.setFailure .connectionClosed, .stop)
  else
    (machine.addEvent (.needMoreData expect), .stop)

/--
Reads `size` body bytes and the `framing` bytes after them, which also count toward `maxBodySize`,
and moves the reader to `next`. Moving to `.complete` ends the body: the chunk is final, and
`.closeBody` is emitted unless the body is an interim response's, which belongs to the final
response. The data is copied only for a caller, and not at all when it is a whole buffer that `feed`
received.
-/
private def readBodyBytes (machine : Machine dir) (size : Nat) (next : Reader.State)
    (framing := 0) (incomplete := false)
    (extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue) := #[]) :
    Machine dir × BodyStep :=
  let read := size + framing
  if machine.reader.bodyBytesRead + read > machine.config.maxBodySize then
    (machine.setFailure .entityTooLarge, .stop)
  else
    let input := machine.reader.input
    let final := next matches .complete
    let machine := machine.modifyReader fun reader =>
      { reader with
        input := input.forward read
        bodyBytesRead := reader.bodyBytesRead + read
        state := next
        inMessage := reader.inMessage && !final }
    let machine := if final then machine.addEvent .closeBody else machine
    if machine.readsBodyItself then
      (machine, .next)
    else
      let bytes := input.array
      let data :=
        if size == 0 then .empty
        else if input.pos == 0 && size == bytes.size then bytes
        else bytes.extract input.pos (input.pos + size)
      (machine, .chunk { final, incomplete, chunk := { data, extensions } })

/--
Reads fixed-length body bytes, `size` of which are left.
-/
private def readFixedBody (machine : Machine dir) (size : Nat) : Machine dir × BodyStep :=
  let available := machine.reader.remainingBytes
  if available = 0 then
    waitForBody machine (some size)
  else if available < size then
    readBodyBytes machine available (.readBody (.fixed (size - available)))
  else
    readBodyBytes machine size .complete

/--
Where a line break (`\r\n`) is expected: present, cut off by the end of the input, or wrong.
-/
private inductive LineBreak where
  | ok
  | eof
  | bad

/--
Checks for a line break at position `i` of `bytes`, as `crlf` parses it.
-/
@[inline]
private def lineBreakAt (bytes : ByteArray) (i : Nat) : LineBreak :=
  if h : i < bytes.size then
    if bytes[i] != '\r'.toUInt8 then .bad
    else if h : i + 1 < bytes.size then
      if bytes[i + 1] == '\n'.toUInt8 then .ok else .bad
    else .eof
  else .eof

/--
Reads the data of a chunk, `size` bytes of which are left. The last bytes are read only together
with the line break after them, which counts toward `maxBodySize`.
-/
private def readChunkData (machine : Machine dir)
    (extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (size : Nat) :
    Machine dir × BodyStep :=
  let input := machine.reader.input
  let available := input.remainingBytes
  if available = 0 then
    waitForBody machine (some size)
  else if available < size then
    readBodyBytes machine available (.readBody (.chunkedBody extensions (size - available)))
      (incomplete := true) (extensions := extensions)
  else
    match lineBreakAt input.array (input.pos + size) with
    | .ok =>
      readBodyBytes machine size (.readBody .chunkedSize) (framing := 2) (extensions := extensions)
    | .eof => waitForBody machine (some size)
    | .bad => (machine.setFailure .badMessage, .stop)

/--
Reads a chunk-size line. The line, like the line break after the data and the trailer section,
counts toward `maxBodySize`, so the wire size of a chunked body stays bounded however small its
chunks are.
-/
private def readChunkSize (machine : Machine dir) : Machine dir × BodyStep :=
  parseThen machine .chunkLine (parseChunkSize machine.config) .stop
    (limit := some machine.config.maxChunkLineLength) fun machine (size, extensions) length =>
      if size > machine.config.maxChunkSize ||
          machine.reader.bodyBytesRead + length + size > machine.config.maxBodySize then
        (machine.setFailure .entityTooLarge, .stop)
      else
        let machine := machine.modifyReader fun reader =>
          { reader with
            bodyBytesRead := reader.bodyBytesRead + length
            state := .readBody (.chunkedBody extensions size) }
        (machine, .next)

/--
Reads one line of the trailer section after the last chunk, `count` fields into it. The empty line
that ends the section ends the body. A field is consumed on its own, as header lines are, so a read
that ends inside the section does not make the next read parse the earlier fields again.
-/
private def readTrailerLine (machine : Machine dir)
    (extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (count : Nat) :
    Machine dir × BodyStep :=
  -- A server rejects every field forbidden in a request's trailers; a client, which discards
  -- trailers, only refuses those that would reframe the response.
  let strict := dir matches .receiving
  if !strict && count > 0 && startsWithWhitespace machine.reader.input then
    -- An obs-fold continues the last trailer field, which a client discards (RFC 9112 §5.2).
    parseThen machine .foldLine (parseObsFoldContinuation machine.config) .stop
        (onError := fun _ => .badMessage) fun machine _ length =>
      if machine.reader.bodyBytesRead + length > machine.config.maxBodySize then
        (machine.setFailure .entityTooLarge, .stop)
      else
        (machine.modifyReader fun r => { r with bodyBytesRead := r.bodyBytesRead + length }, .next)
  else
    parseThen machine .fieldLine (parseTrailerHeader machine.config strict) .stop
        (onError := fun _ => .badMessage) fun machine field length =>
      match field with
      | some _ =>
        if count ≥ machine.config.maxTrailerHeaders then
          (machine.setFailure .badMessage, .stop)
        else if machine.reader.bodyBytesRead + length > machine.config.maxBodySize then
          (machine.setFailure .entityTooLarge, .stop)
        else
          let machine := machine.modifyReader fun reader =>
            { reader with
              bodyBytesRead := reader.bodyBytesRead + length
              state := .readBody (.trailers extensions (count + 1)) }
          (machine, .next)
      | none =>
        let machine :=
          machine.modifyReader fun r => { r with bodyBytesRead := r.bodyBytesRead + length }
        readBodyBytes machine 0 .complete (extensions := extensions)

/--
Reads the bytes of a body that ends when the connection closes.
-/
private def readCloseDelimitedBody (machine : Machine dir) : Machine dir × BodyStep :=
  let available := machine.reader.remainingBytes
  if available ≠ 0 then
    readBodyBytes machine available (.readBody .closeDelimited)
  else if machine.reader.noMoreInput then
    readBodyBytes machine 0 .complete
  else
    (machine.addEvent (.needMoreData none), .stop)

/--
One body transition, by framing state.
-/
private def bodyStep (machine : Machine dir) : Reader.BodyState → Machine dir × BodyStep
  | .fixed 0 => readBodyBytes machine 0 .complete
  | .fixed size => readFixedBody machine size
  | .chunkedSize => readChunkSize machine
  | .chunkedBody extensions 0 => readTrailerLine machine extensions 0
  | .chunkedBody extensions size => readChunkData machine extensions size
  | .trailers extensions count => readTrailerLine machine extensions count
  | .closeDelimited => readCloseDelimitedBody machine

/-! #### Termination -/

private theorem remainingBytes_forward (it : ByteArray.Iterator) (n : Nat) :
    (it.forward n).remainingBytes = it.remainingBytes - n := by
  cases it
  simp only [ByteArray.Iterator.forward, ByteArray.Iterator.remainingBytes]
  omega

private theorem lineBreakAt_ok {it : ByteArray.Iterator}
    (h : lineBreakAt it.array (it.pos + n) = .ok) : n + 2 ≤ it.remainingBytes := by
  have : it.pos + n + 1 < it.array.size := by
    unfold lineBreakAt at h
    split at h
    · split at h
      · cases h
      · split at h
        · assumption
        · cases h
    · cases h
  obtain ⟨array, i⟩ := it
  simp only [ByteArray.Iterator.pos, ByteArray.Iterator.remainingBytes] at this ⊢
  omega

private theorem readBodyBytes_decreases (m : Machine dir) (size : Nat) (next : Reader.State)
    (framing : Nat) (incomplete : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (hle : size + framing ≤ m.reader.remainingBytes)
    (hprog : 0 < size + framing ∨ next = .complete) :
    (readBodyBytes m size next framing incomplete ext).2 ≠ .stop →
      (readBodyBytes m size next framing incomplete ext).1.reader.remainingBytes <
          m.reader.remainingBytes ∨
        (readBodyBytes m size next framing incomplete ext).1.reader.state = .complete := by
  unfold readBodyBytes
  dsimp only
  have key (x : Machine dir) (hi : x.reader.input = m.reader.input.forward (size + framing))
      (hs : x.reader.state = next) :
      x.reader.remainingBytes < m.reader.remainingBytes ∨ x.reader.state = .complete := by
    rcases hprog with h | h
    · have := remainingBytes_forward m.reader.input (size + framing)
      simp only [Reader.remainingBytes_eq, hi] at this hle ⊢
      omega
    · exact .inr (hs.trans h)
  split
  · simp
  · intro _
    (repeat' split) <;> exact key _ rfl rfl

private theorem readBodyBytes_complete (m : Machine dir) ext :
    (readBodyBytes m 0 .complete 0 false ext).1.reader.input.remainingBytes =
      m.reader.input.remainingBytes := by
  unfold readBodyBytes
  dsimp only
  (repeat' split) <;> simp [setFailure, addEvent, modifyReader, remainingBytes_forward]

/--
An item `parseThen` accepts is at least one byte long, so if `next` keeps the input it was given, a
`parseThen` that does not stop leaves fewer unread bytes.
-/
private theorem parseThen_decreases {m : Machine dir} {kind : LineKind} {p : Parser α} {stop : β}
    {next : Machine dir → α → Nat → Machine dir × β} {limit : Option Nat}
    {onError : Std.Internal.Parsec.Error → H1.Error}
    (hnext : ∀ m' a n, (next m' a n).1.reader.remainingBytes = m'.reader.remainingBytes) :
    (parseThen m kind p stop next limit onError).2 ≠ stop →
      (parseThen m kind p stop next limit onError).1.reader.remainingBytes <
        m.reader.remainingBytes := by
  unfold parseThen
  dsimp only
  split
  · simp
  · split
    · rename_i rest result _
      split
      · simp
      · rename_i hlen
        intro _
        rw [hnext]
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hlen
        simp only [modifyReader, Reader.remainingBytes_eq, Reader.input_setInput]
        omega
    · split <;> (try split) <;> simp
    · simp

section
attribute [local simp] Reader.remainingBytes_eq setFailure addEvent setReaderState modifyReader
  readBodyBytes_complete

/--
A body transition that does not stop reads input or ends the body.
-/
private theorem bodyStep_decreases (m : Machine dir) (s : Reader.BodyState) :
    (bodyStep m s).2 ≠ .stop →
      (bodyStep m s).1.reader.remainingBytes < m.reader.remainingBytes ∨
        (bodyStep m s).1.reader.state = .complete := by
  have hwait (e) : (waitForBody m e).2 = .stop := by unfold waitForBody; split <;> rfl
  unfold bodyStep
  -- Unfold the transitions and split their branches; then each branch stops, reads body bytes, or
  -- parses an item.
  split <;>
    repeat' first
      | split
      | (unfold readFixedBody; try dsimp only)
      | (unfold readChunkData; try dsimp only)
      | (unfold readCloseDelimitedBody; try dsimp only)
      | (unfold readChunkSize; try dsimp only)
      | (unfold readTrailerLine; try dsimp only)
  all_goals first
    | (simp [hwait]; done)
    | exact readBodyBytes_decreases _ _ _ _ _ _ (by simp only [Reader.remainingBytes_eq] at *; omega)
        (.inr rfl)
    | exact readBodyBytes_decreases _ _ _ _ _ _ (by simp only [Reader.remainingBytes_eq] at *; omega)
        (.inl (by omega))
    | exact readBodyBytes_decreases _ _ _ _ _ _
        (by rw [Reader.remainingBytes_eq]; exact lineBreakAt_ok ‹_›) (.inl (by omega))
    | (intro h
       exact .inl (parseThen_decreases (by intro _ _ _; (repeat' split) <;> simp) h))

end

/--
Runs body transitions until one produces a chunk or waits, or the body ends.
-/
private def pullLoop (machine : Machine dir) : Machine dir × Option PulledChunk :=
  match _hs : machine.reader.state with
  | .readBody state =>
    match _h : bodyStep machine state with
    | (next, .chunk pulled) => (next, some pulled)
    | (next, .next) =>
      if _hb : next.reader.state matches .readBody _ then pullLoop next else (next, none)
    | (next, .stop) => (next, none)
  | _ => (machine, none)
termination_by machine.reader.remainingBytes
decreasing_by
  have := bodyStep_decreases machine state
  simp only [_h, ne_eq, reduceCtorEq, not_false_eq_true, forall_const] at this
  rcases this with h | h
  · exact h
  · simp [h] at _hb

/-! #### Message heads -/

/--
Starts reading the header section of a message whose start line gave `head`.
-/
@[inline]
private def startHeaders (machine : Machine dir) (head : Message.Head dir) : Machine dir :=
  machine.modifyReader fun reader => { reader with messageHead := head, state := .needHeader 0 }

/--
Whether the unread input holds nothing but `CR` and `LF` bytes. Scans in place and stops at the
first other byte.
-/
@[inline]
private def onlyLineEndsLeft (input : ByteArray.Iterator) : Bool :=
  (input.array.findIdx? (fun b => b != '\r'.toUInt8 && b != '\n'.toUInt8) input.pos).isNone

/--
`needStartLine`: ends the reader when the input is over, waits when it is empty, and otherwise reads
the request or status line. A server ignores empty lines before a request line (RFC 9112 §2.2), so
input that ends with nothing else ends the reader as plain EOF does. A client reads a status line
only once its request is sent, so the end of input there leaves the exchange without a final
response, which is incomplete (RFC 9112 §8).

A request line's `maxStartLineLength` is checked on the complete line only: on an incomplete line it
would fire before the parser's `maxUriLength` check, so the status would depend on where a read
ends. The parser's own limits (leading empty lines, method, `maxUriLength`) bound an incomplete
line. An HTTP/1.0 response is accepted, and `shouldKeepAlive` then ends the connection after it. The
heads of interim responses count toward `maxHeaderBytes` together with the final head's fields, so
a run of 1xx responses is bounded.
-/
@[inline]
private def readStartLine (machine : Machine dir) : Machine dir × Bool :=
  let input := machine.reader.input
  let onlyLineEnds := (dir matches .receiving) && onlyLineEndsLeft input
  if machine.reader.noMoreInput && (input.atEnd || onlyLineEnds) then
    match dir with
    | .receiving => (machine.setReaderState .closed, false)
    | .sending => (machine.setFailure .connectionClosed, false)
  else if input.atEnd then
    (machine.addEvent (.needMoreData none), false)
  else
    match dir, machine with
    | .receiving, machine =>
      parseThen machine .requestLine (parseRequestLineRawVersion machine.config) false
          fun machine (method, uri, version) length =>
        -- The method and version are bounded, so a line over the limit is over it because of its
        -- target (RFC 9112 §3).
        if length > machine.config.maxStartLineLength then
          (machine.setFailure .uriTooLong, false)
        else
          match version with
          | some (v@Version.v11) | some (v@Version.v10) =>
            (startHeaders machine { method, version := v, uri, headers := .empty }, true)
          | _ => (machine.setFailure .unsupportedVersion, false)
    | .sending, machine =>
      parseThen machine .statusLine (parseStatusLineRawVersion machine.config) false
          (limit := some machine.config.maxStartLineLength) fun machine (status, version) length =>
        let headerBytes := machine.reader.headerBytesRead + if status.isInterim then length else 0
        if headerBytes > machine.config.maxHeaderBytes then
          (machine.setFailure .headersTooLarge, false)
        else
          let machine := machine.modifyReader ({ · with headerBytesRead := headerBytes })
          match version with
          | some (v@Version.v11) | some (v@Version.v10) =>
            (startHeaders machine { status, version := v, headers := .empty }, true)
          | _ => (machine.setFailure .unsupportedVersion, false)

/--
A client reads a header line that starts with whitespace as an obs-fold: it continues the last
field's value, joined with a space (RFC 9112 §5.2). A server rejects it, as the line parser does.
-/
private def readObsFold (machine : Machine dir) : Machine dir × Bool :=
  parseThen machine .foldLine (parseObsFoldContinuation machine.config) false
      fun machine part length =>
    match machine.reader.messageHead.headers.map.entries.back? with
    | none => (machine.setFailure .badMessage, false)
    | some (name, previous) =>
      let value :=
        if part.isEmpty then previous.value
        else if previous.value.isEmpty then part
        else previous.value ++ " " ++ part
      if machine.reader.headerBytesRead + length > machine.config.maxHeaderBytes then
        (machine.setFailure .headersTooLarge, false)
      else if value.utf8ByteSize > machine.config.maxHeaderValueLength then
        (machine.setFailure .headersTooLarge, false)
      else
        match Header.Value.ofString? value with
        | some value =>
          let machine := machine.modifyReader fun reader =>
            { reader with
              messageHead :=
                reader.messageHead.setHeaders (reader.messageHead.headers.replaceLast name value)
              headerBytesRead := reader.headerBytesRead + length }
          (machine, true)
        | none => (machine.setFailure .badMessage, false)

/--
`needHeader count`: reads one header field line, checking the header limits, or the empty line that
ends the header section (`processHeaders`).
-/
@[inline]
private def readHeaderLine (machine : Machine dir) (count : Nat) : Machine dir × Bool :=
  if (dir matches .sending) && count > 0 && startsWithWhitespace machine.reader.input then
    readObsFold machine
  else
    parseThen machine .fieldLine (parseSingleHeader machine.config) false
        fun machine field length =>
      match field with
      | some (name, value) =>
        if count ≥ machine.config.maxHeaders then
          (machine.setFailure .tooManyHeaders, false)
        else if machine.reader.headerBytesRead + length > machine.config.maxHeaderBytes then
          (machine.setFailure .headersTooLarge, false)
        else
          match Header.Name.ofString? name, Header.Value.ofString? value with
          | some name, some value =>
            let machine := machine.modifyReader fun reader =>
              { reader with
                messageHead :=
                  reader.messageHead.setHeaders (reader.messageHead.headers.insert name value)
                headerBytesRead := reader.headerBytesRead + length
                state := .needHeader (count + 1) }
            (machine, true)
          | _, _ => (machine.setFailure .badMessage, false)
      | none => (processHeaders machine, true)

/--
`complete`: the reader closes when no message can follow, because the input is over or keep-alive is
off. After `101 Switching Protocols`, or a 2xx answer to `CONNECT`, the bytes that follow are not
HTTP/1.1 and the connection cannot be reused (`leavesHttp`). Otherwise the reader stays complete
until the writer finishes the exchange.
-/
private def readComplete (machine : Machine dir) : Machine dir :=
  let leaves :=
    match dir, machine with
    | .sending, machine =>
      leavesHttp machine.writer.messageHead.method machine.reader.messageHead.status
    | .receiving, _ => false
  let machine := if leaves then machine.disableKeepAlive else machine
  let reader := machine.reader
  if (reader.noMoreInput ∧ reader.input.atEnd) ∨ ¬machine.keepAlive then
    machine.setReaderState .closed
  else
    machine

/--
`pending`: a client with no request outstanding, before its first request or between exchanges. What
arrives now answers no request (RFC 9112 §9.2), and what is left after a response must not be read
as the next one (RFC 9112 §6.3). Line breaks alone are discarded; anything else leaves the message
boundaries ambiguous, so the machine fails before another request goes out on the connection.
-/
private def readPending (machine : Machine dir) : Machine dir :=
  let input := machine.reader.input
  if machine.writer.state matches .closed then
    machine.setReaderState .closed
  else if input.atEnd then
    machine
  else if onlyLineEndsLeft input then
    machine.modifyReader (·.setInput (input.forward input.remainingBytes))
  else
    closeOnBadMessage machine

/--
One reader transition, by state. Returns `true` when the reader moved to a state that it processes
in the same call. A body the machine reads itself (`readsBodyItself`) is read as far as the input
goes, and the reader moves on if it ends; any other body waits for `pullBody`.
-/
@[inline]
private def readStep (machine : Machine dir) : Machine dir × Bool :=
  match machine.reader.state with
  | .needStartLine => readStartLine machine
  | .needHeader count => readHeaderLine machine count
  | .readBody _ =>
    if machine.readsBodyItself then
      let machine := (pullLoop machine).1
      (if machine.reader.state matches .complete then readComplete machine else machine, false)
    else
      (machine, false)
  | .complete => (readComplete machine, false)
  | .pending => (readPending machine, false)
  | .«continue» _ | .closed => (machine, false)

private theorem processHeaders_input (m : Machine dir) :
    (processHeaders m).reader.input = m.reader.input := by
  unfold processHeaders startBody
  cases dir <;> dsimp only <;> (repeat' split) <;> simp [setFailure, addEvent, setReaderState,
    modifyReader, modifyWriter, setWriterState, disableKeepAlive, limitKeepAlive]

section
attribute [local simp] Reader.remainingBytes_eq setFailure addEvent setReaderState modifyReader
  startHeaders processHeaders_input

/--
A reader transition that asks for another reads input.
-/
private theorem readStep_decreases (m : Machine dir) :
    (readStep m).2 = true → (readStep m).1.reader.remainingBytes < m.reader.remainingBytes := by
  unfold readStep
  -- Not `split`: the splitter it would add for this match is compiled, into ~10 KB of dead code.
  generalize m.reader.state = st
  cases st <;> dsimp only
  all_goals
    repeat' first
      | split
      | (unfold readStartLine; try dsimp only)
      | (unfold readHeaderLine; try dsimp only)
      | (unfold readObsFold; try dsimp only)
  all_goals first
    | (simp; done)
    | (intro h
       exact parseThen_decreases (by intro _ _ _; (repeat' split) <;> simp)
         (Bool.ne_false_of_eq_true h))

end

/--
Runs reader transitions until one waits: for input, for a caller's decision, or for the next `step`.
-/
private def processRead (machine : Machine dir) : Machine dir :=
  match _h : readStep machine with
  | (next, true) => processRead next
  | (next, false) => next
termination_by machine.reader.remainingBytes
decreasing_by have := readStep_decreases machine; simp_all

/--
How far the machine is from halting: fewer messages left to read, or the same exchange further on.
Within an exchange, the reader and the writer only move forward.
-/
private def progress (machine : Machine dir) : Nat :=
  let reader := match machine.reader.state with
    | .needStartLine | .pending => 5
    | .needHeader _ => 4
    | .«continue» _ => 3
    | .readBody _ => 2
    | .complete => 1
    | .closed => 0
  let writer := match machine.writer.state with
    | .pending => 6
    | .waitingHeaders => 5
    | .waitingForFlush => 4
    | .writingBodyFixed _ | .writingBodyOpen _ => 3
    | .complete => 1
    | .closed => 0
  (machine.config.maxMessages - machine.reader.messageCount) * 16 + reader + writer

/--
Runs the reader, then the writer, and again while the writer moved on, which can let the reader go
on: an exchange that ended starts the next, whose head may already be buffered, and a body is
drained once its response is written. A failure closes the reader, and `processWrite` closes a
pending writer once the reader is closed, so the error response (`answerFailure`) is given before
writing. The loop goes on only while `progress` falls, which bounds it without assuming anything of
the transitions.
-/
private def run (machine : Machine dir) : Machine dir :=
  let read := machine.processRead.answerFailure
  let written := read.processWrite
  if _h : progress written < progress read ∧ progress written < progress machine then run written
  else written
termination_by progress machine
decreasing_by exact _h.2

/--
Execute one step of the state machine: it runs until it waits for input, for the caller, or for its
output to be taken.
-/
@[inline]
def step (machine : Machine dir) : Machine dir × StepResult dir :=
  let machine := machine.run
  let (machine, events) := machine.takeEvents
  let output := machine.writer.outputData
  ({ machine with writer := { machine.writer with outputData := .empty } }, { events, output })

/--
Pulls at most one body chunk from the reader: it reads body framing until it produces a chunk, or
returns `none` when it has to wait for input, failed, or the body cannot be pulled (`canPullBody`).
-/
@[inline]
def pullBody (machine : Machine dir) : Machine dir × Option PulledChunk :=
  if machine.canPullBody then pullLoop machine else (machine, none)

end Std.Http.Protocol.H1.Machine
