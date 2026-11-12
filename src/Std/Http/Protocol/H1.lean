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
private def setReaderState (machine : Machine dir) (state : Reader.State dir) : Machine dir :=
  machine.modifyReader ({ · with state })

@[inline]
private def setWriterState (machine : Machine dir) (state : Writer.State) : Machine dir :=
  machine.modifyWriter ({ · with state })

@[inline]
private def addEvent (machine : Machine dir) (event : Event dir) : Machine dir :=
  { machine with events := machine.events.push event }

@[inline]
private def setError (machine : Machine dir) (error : Error) : Machine dir :=
  { machine with error := some error }

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

@[inline]
private def failBadMessage (machine : Machine dir) : Machine dir :=
  machine.setFailure .badMessage

private def updateKeepAlive (machine : Machine dir) (should : Bool) : Machine dir :=
  { machine with keepAlive := machine.keepAlive ∧ should }

/--
Checks the head the reader just finished and chooses how to read its body.
-/
private def checkMessageHead (machine : Machine dir) : Except Error Reader.BodyState :=
  match dir with
  | .receiving => checkRequestHead machine.config machine.reader.messageHead
  | .sending => checkResponseHead machine.writer.messageHead.method machine.reader.messageHead

/--
Applies the keep-alive limits of an exchange with a message head `head`: `maxMessages`, and what
`head`'s `Connection` field says.
-/
@[inline]
private def limitKeepAlive (machine : Machine dir) (head : Message.Head d) : Machine dir :=
  machine.updateKeepAlive
    (machine.reader.messageCount + 1 < machine.config.maxMessages && head.shouldKeepAlive)

/--
Returns `true` when the body being read belongs to an interim (1xx) response. Such a response has no
message body of its own: it is part of an exchange whose final response is still to come.
-/
@[inline]
private def isInterimResponseBody (machine : Machine dir) : Bool :=
  match dir with
  | .receiving => false
  | .sending => machine.reader.messageHead.status.isInterim

/--
Whether the machine reads the body itself instead of leaving it to `pullBody`. A server drains the
rest of a request body once its response is fully written: until then the handler may still read it,
for example to stream it back. An empty remainder has nothing to deliver, so it is read as soon as
the response head is given, and an empty response body as soon as it starts, since it has no bytes
to expose and would otherwise stall the connection (204, 304, HEAD responses). A client also drains
an interim response's body.
-/
@[inline]
private def readsBodyItself (machine : Machine dir) : Bool :=
  let emptyRest := machine.reader.state matches .readBody (.fixed 0)
  match dir with
  | .receiving =>
    (machine.writer.state matches .complete | .closed) || (machine.writer.sentMessage && emptyRest)
  | .sending => machine.isInterimResponseBody || emptyRest

/--
Upper bound for unread input retained in memory at once.

This caps buffered body bytes and parser lookahead (start-line/headers/chunk
metadata) so a stalled consumer cannot accumulate unbounded pending input.
-/
@[inline]
private def maxBufferedInputBytes (config : Config) : Nat :=
  config.maxBodySize + config.maxHeaderBytes + config.maxStartLineLength + config.maxChunkLineLength

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
  match dir, machine.reader.state with
  | .receiving, .«continue» _ => true
  | _, _ => false

/--
Whether the outgoing message is an HTTP/1.0 request, which cannot be chunked (RFC 9112 §6.1) and
cannot end with the connection either.
-/
@[inline]
private def isHttp10Request (machine : Machine dir) : Bool :=
  (dir matches .sending) && machine.writer.messageHead.version == .v10

/--
Whether the head given to `send` can be written: its body's framing is known, or the exchange is
over. Body data counts, so a streamed body starts going out before it ends, except in an HTTP/1.0
request: it cannot be chunked (RFC 9112 §6.1), so unless its length was set it waits for its whole
body.
-/
@[inline]
def shouldFlush (machine : Machine dir) : Bool :=
  machine.failed ∨
  machine.reader.state == .closed ∨
  machine.writer.noMoreUserData ∨
  machine.writer.knownSize.isSome ∨
  (machine.writer.userData.size > 0 ∧ ¬machine.isHttp10Request)

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
Whether the peer may still be sending when the connection ends: it has not closed its side, and a
message is unfinished, or the machine still took input when it stopped, after failing or with input
it never read. Closing a connection with unread input resets it, which can destroy the last response
before the peer reads it (RFC 9112 §9.6).
-/
def peerMayStillSend (machine : Machine dir) : Bool :=
  let reader := machine.reader
  !reader.peerClosed &&
    (reader.inMessage || (!reader.inputStopped && (machine.failed || reader.remainingBytes > 0)))

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
waits for the response, and first for a `canContinue` decision when the request expects one.
-/
private def startBody (machine : Machine dir) (body : Reader.BodyState) : Machine dir :=
  let head := machine.reader.messageHead
  let machine := { machine with reader := { machine.reader with inMessage := true } }
  let machine := machine.addEvent (.endHeaders head)
  match dir, machine, head with
  | .receiving, machine, head =>
    let machine :=
      if expectsContinue head then
        machine.addEvent .«continue» |>.setReaderState (.«continue» (.readBody body))
      else
        machine.setReaderState (.readBody body)
    machine.setWriterState .waitingHeaders |>.addEvent .needAnswer
  | .sending, machine, _ => machine.setReaderState (.readBody body)

/--
Ends the header section: applies the keep-alive limits, checks the head, and starts its body. A body
that ends with the connection turns keep-alive off.
-/
private def processHeaders (machine : Machine dir) : Machine dir :=
  let machine := machine.limitKeepAlive machine.reader.messageHead
  match checkMessageHead machine with
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
Writes the head of the outgoing message and enters the state that writes its body. A final response
written while an `Expect: 100-continue` decision is pending ends the exchange without the body
(`processCompleteStep`), so its head says `close` (RFC 9110 §10.1.1).
-/
private def writeHead (messageHead : Message.Head dir.swap) (machine : Machine dir) : Machine dir :=
  let machine := machine.limitKeepAlive messageHead
  let machine := if machine.isReaderAwaitingContinue then machine.disableKeepAlive else machine
  let size := Writer.determineTransferMode machine.writer
  -- RFC 9110 §15.3.6: a 205 response is framed as empty, whatever length was set for its body.
  let size : Body.Length :=
    match dir, messageHead with
    | .receiving, messageHead => if messageHead.status.contentRule == .empty then .fixed 0 else size
    | .sending, _ => size
  -- HTTP/1.0 has no chunked coding: a response of unknown length ends when the connection closes,
  -- unless its body is omitted (a HEAD response), which leaves nothing to delimit.
  let version := machine.reader.messageHead.version
  let closeDelimited := (dir matches .receiving) && version == .v10 && size == .chunked
  let machine :=
    if closeDelimited && !machine.writer.omitBody then machine.disableKeepAlive else machine
  let state : Writer.State :=
    match size with
    | .fixed n => .writingBodyFixed n
    | .chunked => if closeDelimited then .writingBodyClosingFrame else .writingBodyChunked
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
  if machine.isReaderClosed ∨ machine.failed then
    machine
  else
    let reader := machine.reader.feed data
    let machine := { machine with reader }
    if reader.remainingBytes > maxBufferedInputBytes machine.config then
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
Set a known size for the message body, replacing any previous value.
-/
@[inline]
def setKnownSize (machine : Machine dir) (size : Body.Length) : Machine dir :=
  machine.modifyWriter (fun w => { w with knownSize := some size })

/--
Reconciles the body length the caller set (`knownSize`) with the framing fields of the message head
passed to `send`. The fields' length is adopted when none was set, or when only `chunked` was, which
leaves the length unknown (a `Body.stream` starts that way). Returns `none` when the two contradict,
or when the fields describe no length.
-/
private def reconcileOutgoingFraming (machine : Machine dir)
    (headerSize : Option Body.Length) (framingInHeaders : Bool) : Option (Machine dir) :=
  match machine.writer.knownSize, headerSize with
  | some explicit, some parsed =>
    if explicit == parsed then some machine
    -- The fixed-length writer closes the connection if the body then runs over or falls short.
    else if explicit == .chunked then some (machine.setKnownSize parsed)
    else none
  | none, some parsed => some (machine.setKnownSize parsed)
  | _, none => if framingInHeaders then none else some machine

/--
The failure `rejectOutgoingFraming` reports: a mistake of the sender's own code, not a malformed
message from the peer. A server passes it to `Handler.onFailure`.
-/
private def framingMismatchError : H1.Error :=
  .other "Content-Length or Transfer-Encoding contradicts the body"

/--
Handles a message head that `reconcileOutgoingFraming` rejected. None of that message is written:
a server answers `500 Internal Server Error` with a short `text/plain` explanation and closes the
connection, and a client ends the exchange. Both report `framingMismatchError`, and the machine
halts once its output is taken.
-/
private def rejectOutgoingFraming (machine : Machine dir) : Machine dir :=
  let machine := machine
    |>.addEvent (.failed framingMismatchError)
    |>.setError framingMismatchError
    |>.stopReading
  match dir, machine with
  | .receiving, machine =>
    -- The 500 is written here, not by the writer, because `omitBody` must stay set: it makes the
    -- connection drop the handler's body instead of draining it, and the writer drops omitted
    -- content.
    let (head, content) := errorResponse .internalServerError
    let encoded := encodeResponseHead head machine.reader.messageHead.version machine.keepAlive
      machine.date machine.config.agentName (.fixed content.size)
    machine.modifyWriter fun w => { w with
      messageHead := head, state := .complete, omitBody := true, userClosedBody := true
      userData := #[], userDataBytes := 0, outputData := w.outputData.push encoded |>.push content }
  | .sending, machine => machine.closeWriter

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
    { w with
      omitBody := true, userClosedBody := true, knownSize, userData := #[], userDataBytes := 0 }

/--
Writes an informational (1xx) response at once. It has no content, so framing fields the caller set
are left out (RFC 9110 §15.2), and a server never sends one to an HTTP/1.0 client.
-/
private def sendInterim (machine : Machine .receiving) (head : Response.Head) :
    Machine .receiving :=
  if machine.reader.messageHead.version != .v11 then
    machine
  else
    let head : Response.Head := { head with
      headers := head.headers
        |>.erase Header.Name.contentLength
        |>.erase Header.Name.transferEncoding }
    machine.modifyWriter fun w =>
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
decision.

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
      if message.status.isInterim then
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
    match reconciled with
    | none => rejectOutgoingFraming machine
    | some machine =>
      if !omits && unframeableForHttp10 machine message then
        rejectOutgoingFraming machine
      else
        let machine :=
          machine.modifyWriter ({ · with messageHead := message, state := .waitingForFlush })
        match dir, machine, message with
        | .sending, machine, _ => machine.setReaderState .needStartLine
        | .receiving, machine, message =>
          let machine := if omits then machine.omitResponseBody message.status else machine
          -- What follows a tunnel's head is not HTTP, and this server does not tunnel.
          if startsTunnel machine.reader.messageHead.method message.status then machine.stopReading
          else machine

/--
Enqueues body chunks into the writer buffer for encoding and sending.
-/
@[inline]
def sendData (machine : Machine dir) (data : Array Chunk) : Machine dir :=
  if data.isEmpty then
    machine
  else
    machine.modifyWriter (fun writer =>
      let extraBytes := data.foldl (fun acc c => acc + c.data.size) 0
      { writer with
        userData := writer.userData ++ data
        userDataBytes := writer.userDataBytes + extraBytes })

/--
Sends a response the machine writes itself (`errorResponse`) with `text/plain` content, which
RFC 9110 §15.5 and §15.6 ask of 4xx and 5xx responses. A response to `HEAD` omits the content and
keeps its `Content-Length`. Does nothing once a response is under way, whose length and body it
would otherwise replace.
-/
private def sendError (machine : Machine .receiving) (status : Status)
    (headers : Headers := .empty) :
    Machine .receiving :=
  if !machine.isWaitingMessage then
    machine
  else
    let (head, content) := errorResponse status headers
    machine
    |>.setKnownSize (.fixed content.size)
    |>.sendData #[{ data := content }]
    |>.send head
    |>.userClosedBody

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
  | .receiving, Reader.State.«continue» nextState =>
    if status == .«continue» then
      machine.sendInterim { status := .«continue» } |>.setReaderState nextState
    else
      machine.sendError status |>.stopReading
  | .receiving, _ => machine

/--
Ends the connection with an error: answers `status` with `Connection: close` and a short
`text/plain` explanation if no response was started, and otherwise stops writing the one under way.
No more input is read.
-/
def closeWithError (machine : Machine .receiving) (status : Status) : Machine .receiving :=
  if machine.isWaitingMessage then
    machine.sendError status (.empty |>.insert .connection (.mk "close")) |>.stopInput
  else
    -- With keep-alive on, a reader that finished its request would wait for the next one whenever
    -- unread input follows it, and the machine would never halt.
    machine.disableKeepAlive.closeWriter.stopInput

/--
Takes and clears all accumulated events, returning the drained array.
-/
@[inline]
def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/--
Takes and clears accumulated output bytes, returning them as a buffer.
-/
@[inline]
def takeOutput (machine : Machine dir) : Machine dir × ChunkedBuffer :=
  let output := machine.writer.outputData
  ({ machine with writer := { machine.writer with outputData := .empty } }, output)

/--
Ends the connection after a mistake of the sender's own code, such as a body longer or shorter than
its stated length: nothing more is read or written. The message on the wire is cut short, so a
server reports it to `Handler.onFailure`.
-/
@[inline]
private def closeOnBadMessage (machine : Machine dir) : Machine dir :=
  machine.addEvent (.failed .badMessage) |>.setError .badMessage |>.stopReading |>.closeWriter
    |>.addEvent .close

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
Marks the message written and moves on (`processCompleteStep`).
-/
@[inline]
private def completeWriterMessage (machine : Machine dir) : Machine dir :=
  processCompleteStep (machine.setWriterState .complete)

/--
Completes a message whose body is left off the wire, dropping any body data given.
-/
@[inline]
private def completeOmittedBody (machine : Machine dir) : Machine dir :=
  completeWriterMessage (machine.modifyWriter ({ · with userData := #[], userDataBytes := 0 }))

/--
Writes a body of stated length, `n` bytes of which are left. A body that runs over or ends short of
the length ends the connection, since the peer would read the next message from the wrong place. The
last bytes are held back until the body is closed, so that a late extra chunk is still caught.
-/
private def processFixedBody (machine : Machine dir) (n : Nat) : Machine dir :=
  let writer := machine.writer
  if writer.omitBody then
    completeOmittedBody machine
  else if writer.userDataBytes > n || (n = 0 && writer.userData.size > 0) then
    closeOnBadMessage machine
  else if !writer.userClosedBody then
    if writer.userData.isEmpty || writer.userDataBytes = n then machine
    else
      let remaining := n - writer.userDataBytes
      { machine with writer := { writer.writeRawBody with state := .writingBodyFixed remaining } }
  else
    let machine := { machine with writer := writer.writeRawBody }
    if writer.userDataBytes < n then closeOnBadMessage machine else completeWriterMessage machine

/--
Writes a chunked body, or the body of an HTTP/1.0 response that ends when the connection closes.
-/
private def processOpenEndedBody (machine : Machine dir) (chunked : Bool) : Machine dir :=
  if machine.writer.omitBody then
    completeOmittedBody machine
  else if machine.writer.userClosedBody then
    completeWriterMessage
      (machine.modifyWriter (if chunked then Writer.writeFinalChunk else Writer.writeRawBody))
  else if machine.writer.userData.size > 0 then
    machine.modifyWriter (if chunked then Writer.writeChunkedBody else Writer.writeRawBody)
  else
    machine

/--
Writes body bytes in one of the `writingBody…` states.
-/
private def processWriteBody (machine : Machine dir) : Machine dir :=
  match machine.writer.state with
  | .writingBodyFixed n => processFixedBody machine n
  | .writingBodyChunked => processOpenEndedBody machine (chunked := true)
  | .writingBodyClosingFrame => processOpenEndedBody machine (chunked := false)
  | _ => machine

/--
Advances writer-side state machine by one logical transition.

Depending on writer state, this may:
- request an application answer,
- serialize headers,
- flush fixed/chunked body bytes,
- finalize/close after completion.
-/
def processWrite (machine : Machine dir) : Machine dir :=
  match machine.writer.state with
  | .pending =>
    if machine.reader.isClosed then machine.closeWriter else machine
  | .waitingHeaders =>
    match dir with
    | .receiving =>
      -- Misuse: the body was closed without a final response, as after only a 1xx interim `send`.
      if machine.writer.userClosedBody then closeOnBadMessage machine else machine
    | .sending => machine.addEvent .needAnswer
  | .waitingForFlush =>
    if machine.shouldFlush then
      -- `writeHead` always enters a `writingBody…` state.
      machine.writeHead machine.writer.messageHead
      |> processWriteBody
    else
      machine
  | .writingBodyFixed _ | .writingBodyChunked | .writingBodyClosingFrame =>
    processWriteBody machine
  | .complete =>
    processCompleteStep machine
  | .closed =>
    machine

/--
A server answers a failure with one error response, with a short `text/plain` explanation, unless a
response was already started. The response it gives makes `sentMessage` hold, so later steps do
nothing.
-/
private def answerFailure (machine : Machine dir) : Machine dir :=
  match dir with
  | .receiving =>
    match machine.error with
    | some error =>
      if machine.writer.sentMessage then machine
      else machine.setWriterState .waitingHeaders |>.sendError error.responseStatus
    | none => machine
  | .sending => machine

/-!
### Reading

The reader advances one transition at a time (`readStep`), and `processRead` runs transitions until
one of them waits: for input, for a caller's decision, or for the next `step`. Every transition that
goes on consumes input or ends a body, so it lowers `readMeasure` (`readStep_decreases`). The proof
needs nothing about the parsers, which are `partial`: `parseThen` fails an item that consumed no
input.

The reader transitions are inlined into `processRead`, so the pairs they return and the parser
closures are not allocated. Body transitions go through `bodyStep`, once per chunk.
-/

/--
The reader loops' termination measure: two units per unread byte, and one more while a body is read,
since a body can end without reading a byte (an empty body, or the end of input).
-/
@[inline]
private def readMeasure (machine : Machine dir) : Nat :=
  2 * machine.reader.remainingBytes + if machine.reader.state matches .readBody _ then 1 else 0

/--
Whether a line feed follows the first `skip` unread bytes.
-/
@[inline]
private def lineFeedAfter (input : ByteArray.Iterator) (skip : Nat) : Bool :=
  go input.array (input.pos + skip)
where
  go (bytes : ByteArray) (i : Nat) : Bool :=
    if h : i < bytes.size then bytes[i] == '\n'.toUInt8 || go bytes (i + 1) else false
  termination_by bytes.size - i

/--
Runs `parser` on the unread input. On success it continues with `next`, given the machine with the
input advanced past the item, the parsed value, and the item's length in bytes. Otherwise the reader
stops with `stop`. When the input ends inside the item, it asks for more, unless no more input will
come (`connectionClosed`) or the item has already reached `limit` bytes (`badMessage`). Malformed
bytes fail with `onError`, and a complete item longer than `limit` fails with `badMessage`.

Every item ends in a line feed. After an incomplete attempt, the parser runs again only when a line
feed has arrived since, when the input reaches `maxLine` bytes (where the parser's own limits
decide), or when the input is over. A malformed byte that arrives after an incomplete attempt is
therefore reported when its line ends.
-/
@[inline]
private def parseThen (machine : Machine dir) (parser : Parser α) (stop : β) (maxLine : Nat)
    (next : Machine dir → α → Nat → Machine dir × β) (limit : Option Nat := none)
    (onError : Std.Internal.Parsec.Error → H1.Error := fun _ => .badMessage) : Machine dir × β :=
  let input := machine.reader.input
  let tried := machine.reader.tried
  if tried != 0 && !machine.reader.noMoreInput && input.remainingBytes < maxLine &&
      !lineFeedAfter input tried then
    let machine := machine.modifyReader ({ · with tried := input.remainingBytes })
    (machine.addEvent (.needMoreData none), stop)
  else
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
        let machine := machine.modifyReader ({ · with tried := input.remainingBytes })
        (machine.addEvent (.needMoreData none), stop)
    | .error _ err =>
      (machine.setFailure (onError err), stop)

/--
The longest field line the parser can still complete: past it, the line fails on a limit.
-/
@[inline]
private def maxFieldLine (config : Config) : Nat :=
  config.maxHeaderNameLength + config.maxHeaderValueLength + 2 * config.maxSpaceSequence + 3

/--
Whether the unread input starts with a space or a tab, as an obs-fold line does.
-/
@[inline]
private def startsWithWhitespace (input : ByteArray.Iterator) : Bool :=
  match input.array[input.pos]? with
  | some b => b == ' '.toUInt8 || b == '\t'.toUInt8
  | none => false

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
private def readBodyBytes (machine : Machine dir) (size : Nat) (next : Reader.State dir)
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
    let machine :=
      if final && !machine.isInterimResponseBody then machine.addEvent .closeBody else machine
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
Ends a body that has no bytes left to read.
-/
@[inline]
private def endBody (machine : Machine dir)
    (extensions : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue) := #[]) :
    Machine dir × BodyStep :=
  readBodyBytes machine 0 .complete (extensions := extensions)

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
    | .bad => (machine.failBadMessage, .stop)

/--
Reads a chunk-size line. The line, like the line break after the data and the trailer section,
counts toward `maxBodySize`, so the wire size of a chunked body stays bounded however small its
chunks are.
-/
private def readChunkSize (machine : Machine dir) : Machine dir × BodyStep :=
  parseThen machine (parseChunkSize machine.config) .stop machine.config.maxChunkLineLength
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
    parseThen machine (parseObsFoldContinuation machine.config) .stop (maxFieldLine machine.config)
        fun machine _ length =>
      if machine.reader.bodyBytesRead + length > machine.config.maxBodySize then
        (machine.setFailure .entityTooLarge, .stop)
      else
        (machine.modifyReader (·.addBodyBytes length), .next)
  else
    parseThen machine (parseTrailerHeader machine.config strict) .stop (maxFieldLine machine.config)
        fun machine field length =>
      match field with
      | some _ =>
        if count ≥ machine.config.maxTrailerHeaders then
          (machine.failBadMessage, .stop)
        else if machine.reader.bodyBytesRead + length > machine.config.maxBodySize then
          (machine.setFailure .entityTooLarge, .stop)
        else
          let machine := machine.modifyReader fun reader =>
            { reader with
              bodyBytesRead := reader.bodyBytesRead + length
              state := .readBody (.trailers extensions (count + 1)) }
          (machine, .next)
      | none => endBody (machine.modifyReader (·.addBodyBytes length)) extensions

/--
Reads the bytes of a body that ends when the connection closes.
-/
private def readCloseDelimitedBody (machine : Machine dir) : Machine dir × BodyStep :=
  let available := machine.reader.remainingBytes
  if available ≠ 0 then
    readBodyBytes machine available (.readBody .closeDelimited)
  else if machine.reader.noMoreInput then
    endBody machine
  else
    (machine.addEvent (.needMoreData none), .stop)

/--
One body transition, by framing state.
-/
private def bodyStep (machine : Machine dir) : Reader.BodyState → Machine dir × BodyStep
  | .fixed 0 => endBody machine
  | .fixed size => readFixedBody machine size
  | .chunkedSize => readChunkSize machine
  | .chunkedBody extensions 0 => readTrailerLine machine extensions 0
  | .chunkedBody extensions size => readChunkData machine extensions size
  | .trailers extensions count => readTrailerLine machine extensions count
  | .closeDelimited => readCloseDelimitedBody machine

/-! #### Message heads -/

/--
Classifies hard request start-line parse failures into protocol-level errors.
-/
@[inline]
private def classifyStartLineHardError : Std.Internal.Parsec.Error → H1.Error
  | .other "uri too long" => .uriTooLong
  | .other "unrecognized method" => .unsupportedMethod
  | _ => .badMessage

/--
Starts reading the header section of a message whose start line gave `head`.
-/
@[inline]
private def startHeaders (machine : Machine dir) (head : Message.Head dir) : Machine dir :=
  machine.modifyReader fun reader => { reader with messageHead := head, state := .needHeader 0 }

/--
Reads a request line (server). `maxStartLineLength` is checked on the complete line only: on an
incomplete line it would fire before the parser's `maxUriLength` check, so the status would depend
on where a read ends. The parser's own limits (leading empty lines, method, `maxUriLength`) bound an
incomplete line.
-/
@[inline]
private def readRequestLine (machine : Machine .receiving) : Machine .receiving × Bool :=
  parseThen machine (parseRequestLineRawVersion machine.config) false
    (machine.config.maxStartLineLength + 2 * machine.config.maxLeadingEmptyLines)
    (onError := classifyStartLineHardError) fun machine (method, uri, version) length =>
      -- The method and version are bounded, so a line over the limit is over it because of its
      -- target (RFC 9112 §3).
      if length > machine.config.maxStartLineLength then
        (machine.setFailure .uriTooLong, false)
      else
        match version with
        | some (v@Version.v11) | some (v@Version.v10) =>
          (startHeaders machine { method, version := v, uri, headers := .empty }, true)
        | _ => (machine.setFailure .unsupportedVersion, false)

/--
Reads a status line (client). An HTTP/1.0 response is accepted, and `shouldKeepAlive` then ends the
connection after it. The heads of interim responses count toward `maxHeaderBytes` together with the
final head's fields, so a run of 1xx responses is bounded.
-/
@[inline]
private def readStatusLine (machine : Machine .sending) : Machine .sending × Bool :=
  parseThen machine (parseStatusLineRawVersion machine.config) false
    machine.config.maxStartLineLength
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
    | .receiving, machine => readRequestLine machine
    | .sending, machine => readStatusLine machine

/--
A client reads a header line that starts with whitespace as an obs-fold: it continues the last
field's value, joined with a space (RFC 9112 §5.2). A server rejects it, as the line parser does.
-/
private def readObsFold (machine : Machine dir) : Machine dir × Bool :=
  parseThen machine (parseObsFoldContinuation machine.config) false (maxFieldLine machine.config)
      fun machine part length =>
    match machine.reader.messageHead.headers.map.entries.back? with
    | none => (machine.failBadMessage, false)
    | some (name, previous) =>
      let value :=
        if part.isEmpty then previous.value
        else if previous.value.isEmpty then part
        else previous.value ++ " " ++ part
      if machine.reader.headerBytesRead + length > machine.config.maxHeaderBytes then
        (machine.setFailure .headersTooLarge, false)
      else if value.utf8ByteSize > machine.config.maxHeaderValueLength then
        (machine.failBadMessage, false)
      else
        match Header.Value.ofString? value with
        | some value =>
          let machine := machine.modifyReader fun reader =>
            { reader with
              messageHead :=
                reader.messageHead.setHeaders (reader.messageHead.headers.replaceLast name value)
              headerBytesRead := reader.headerBytesRead + length }
          (machine, true)
        | none => (machine.failBadMessage, false)

/--
`needHeader count`: reads one header field line, checking the header limits, or the empty line that
ends the header section (`processHeaders`).
-/
@[inline]
private def readHeaderLine (machine : Machine dir) (count : Nat) : Machine dir × Bool :=
  if (dir matches .sending) && count > 0 && startsWithWhitespace machine.reader.input then
    readObsFold machine
  else
    parseThen machine (parseSingleHeader machine.config) false (maxFieldLine machine.config)
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
              { reader.addHeader name value with
                headerBytesRead := reader.headerBytesRead + length
                state := .needHeader (count + 1) }
            (machine, true)
          | _, _ => (machine.failBadMessage, false)
      | none => (processHeaders machine, true)

/--
`readBody`: reads the body when the machine reads it itself (`readsBodyItself`). Otherwise the body
waits for `pullBody`.
-/
@[inline]
private def readBodyItself (machine : Machine dir) (state : Reader.BodyState) :
    Machine dir × Bool :=
  if machine.readsBodyItself then
    let (machine, step) := bodyStep machine state
    (machine, !(step matches .stop))
  else
    (machine, false)

/--
Closes a complete reader when no message can follow, because the input is over or keep-alive is off.
Otherwise it stays complete until the writer finishes the exchange.
-/
@[inline]
private def closeReaderIfDone (machine : Machine dir) : Machine dir :=
  let reader := machine.reader
  if (reader.noMoreInput ∧ reader.input.atEnd) ∨ ¬machine.keepAlive then
    machine.setReaderState .closed
  else
    machine

/--
`complete`: after an interim (1xx) response a client reads the response that follows, in the same
exchange; a 1xx response is not final, so it does not count toward `maxMessages` (RFC 9110 §15.2).
After `101 Switching Protocols`, or a 2xx answer to `CONNECT`, the bytes that follow are not
HTTP/1.1 and the connection cannot be reused (`leavesHttp`). Otherwise the reader closes if no
message can follow.
-/
private def readComplete (machine : Machine dir) : Machine dir :=
  match dir, machine with
  | .sending, machine =>
    let status := machine.reader.messageHead.status
    if status.isInterim then
      machine.modifyReader Reader.resetAfterInterim
    else if leavesHttp machine.writer.messageHead.method status then
      machine.disableKeepAlive.setReaderState .closed
    else
      closeReaderIfDone machine
  | .receiving, machine => closeReaderIfDone machine

/--
One reader transition, by state. Returns `true` when the reader moved to a state that it processes
in the same call.
-/
@[inline]
private def readStep (machine : Machine dir) : Machine dir × Bool :=
  match machine.reader.state with
  | .needStartLine => readStartLine machine
  | .needHeader count => readHeaderLine machine count
  | .readBody state => readBodyItself machine state
  | .complete => (readComplete machine, false)
  | .pending => (if machine.writer.isClosed then machine.setReaderState .closed else machine, false)
  | Reader.State.«continue» _ | .closed => (machine, false)

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

private theorem readMeasure_le (m : Machine dir) :
    readMeasure m ≤ 2 * m.reader.remainingBytes + 1 := by
  unfold readMeasure; split <;> simp

private theorem readMeasure_readBody (m : Machine dir) (h : m.reader.state = .readBody s) :
    readMeasure m = 2 * m.reader.remainingBytes + 1 := by
  simp [readMeasure, h]

private theorem readMeasure_complete (m : Machine dir) (h : m.reader.state = .complete) :
    readMeasure m = 2 * m.reader.remainingBytes := by
  simp [readMeasure, h]

private theorem readMeasure_ge (m : Machine dir) : 2 * m.reader.remainingBytes ≤ readMeasure m := by
  unfold readMeasure; split <;> simp

private theorem readBodyBytes_decreases (m : Machine dir) (size : Nat) (next : Reader.State dir)
    (framing : Nat) (incomplete : Bool)
    (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue))
    (hle : size + framing ≤ m.reader.remainingBytes)
    (hprog : 0 < size + framing ∨ next = .complete) :
    (readBodyBytes m size next framing incomplete ext).2 ≠ .stop →
      readMeasure (readBodyBytes m size next framing incomplete ext).1 <
        2 * m.reader.remainingBytes + 1 := by
  unfold readBodyBytes
  dsimp only
  have key (x : Machine dir) (hi : x.reader.input = m.reader.input.forward (size + framing))
      (hs : x.reader.state = next) : readMeasure x < 2 * m.reader.remainingBytes + 1 := by
    have := remainingBytes_forward m.reader.input (size + framing)
    rcases hprog with h | h
    · have := readMeasure_le x
      simp only [Reader.remainingBytes_eq, hi] at this hle ⊢
      omega
    · have := readMeasure_complete x (hs.trans h)
      simp only [Reader.remainingBytes_eq, hi] at this hle ⊢
      omega
  split
  · simp
  · intro _
    (repeat' split) <;> exact key _ rfl rfl

private theorem processHeaders_input (m : Machine dir) :
    (processHeaders m).reader.input = m.reader.input := by
  unfold processHeaders startBody
  cases dir <;> dsimp only <;> (repeat' split) <;> simp [setFailure, addEvent, setReaderState,
    modifyReader, modifyWriter, setWriterState, disableKeepAlive, limitKeepAlive, updateKeepAlive]

private theorem endBody_remainingBytes (m : Machine dir) ext :
    (endBody m ext).1.reader.input.remainingBytes = m.reader.input.remainingBytes := by
  unfold endBody readBodyBytes
  dsimp only
  (repeat' split) <;> simp [setFailure, addEvent, modifyReader, remainingBytes_forward]

/--
An item `parseThen` accepts is at least one byte long, so if `next` keeps the input it was given, a
`parseThen` that does not stop leaves less than the measure of a reader in any state.
-/
private theorem parseThen_decreases {m : Machine dir} {p : Parser α} {stop : β} {maxLine : Nat}
    {next : Machine dir → α → Nat → Machine dir × β} {limit : Option Nat}
    {onError : Std.Internal.Parsec.Error → H1.Error}
    (hnext : ∀ m' a n, (next m' a n).1.reader.remainingBytes = m'.reader.remainingBytes) :
    (parseThen m p stop maxLine next limit onError).2 ≠ stop →
      readMeasure (parseThen m p stop maxLine next limit onError).1 <
        2 * m.reader.remainingBytes := by
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
        have h1 := readMeasure_le (next (m.modifyReader (·.setInput rest)) result
          (m.reader.input.remainingBytes - rest.remainingBytes)).1
        rw [hnext] at h1
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hlen
        simp only [modifyReader, Reader.remainingBytes_eq, Reader.input_setInput] at h1 ⊢
        omega
    · split <;> (try split) <;> simp
    · simp

section
attribute [local simp] Reader.remainingBytes_eq setFailure failBadMessage addEvent setReaderState
  setError modifyReader startHeaders processHeaders_input endBody_remainingBytes

/--
A body transition that does not stop lowers the measure of a reader reading a body.
-/
private theorem bodyStep_decreases (m : Machine dir) (s : Reader.BodyState) :
    (bodyStep m s).2 ≠ .stop → readMeasure (bodyStep m s).1 < 2 * m.reader.remainingBytes + 1 := by
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
       have := parseThen_decreases (by intro _ _ _; (repeat' split) <;> simp) h
       omega)

private theorem ite_snd_true {c : Prop} [Decidable c] {a b : α × Bool} {P : α → Prop}
    (ha : a.2 = true → P a.1) (hb : b.2 = true → P b.1) :
    (if c then a else b).2 = true → P (if c then a else b).1 := by
  split
  · exact ha
  · exact hb

/--
A reader transition that asks for another lowers `readMeasure`.
-/
private theorem readStep_decreases (m : Machine dir) :
    (readStep m).2 = true → readMeasure (readStep m).1 < readMeasure m := by
  have := readMeasure_ge m
  have hm : readMeasure m =
      2 * m.reader.remainingBytes + if m.reader.state matches .readBody _ then 1 else 0 := rfl
  unfold readStep
  rw [hm]
  -- Not `split`: the splitter it would add for this match is compiled, into ~10 KB of dead code.
  generalize m.reader.state = st
  cases st <;> dsimp only
  case readBody s =>
    unfold readBodyItself
    refine ite_snd_true (P := (readMeasure · < _)) ?_ (by simp)
    have := bodyStep_decreases m s
    revert this
    cases bodyStep m s with | mk m' step => cases step <;> simp
  all_goals
    repeat' first
      | split
      | (unfold readStartLine; try dsimp only)
      | (unfold readRequestLine; try dsimp only)
      | (unfold readStatusLine; try dsimp only)
      | (unfold readHeaderLine; try dsimp only)
      | (unfold readObsFold; try dsimp only)
  all_goals first
    | (simp; done)
    | (intro h
       have := parseThen_decreases (by intro _ _ _; (repeat' split) <;> simp)
         (Bool.ne_false_of_eq_true h)
       omega)

end

/--
Runs reader transitions until one waits: for input, for a caller's decision, or for the next `step`.
-/
def processRead (machine : Machine dir) : Machine dir :=
  match _h : readStep machine with
  | (next, true) => processRead next
  | (next, false) => next
termination_by readMeasure machine
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
    | .writingBodyFixed _ | .writingBodyChunked | .writingBodyClosingFrame => 3
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
  let (machine, output) := machine.takeOutput
  (machine, { events, output })

/--
Runs body transitions until one produces a chunk or waits.
-/
private def pullLoop (machine : Machine dir) : Machine dir × Option PulledChunk :=
  match _hs : machine.reader.state with
  | .readBody state =>
    match _h : bodyStep machine state with
    | (next, .chunk pulled) => (next, some pulled)
    | (next, .next) => pullLoop next
    | (next, .stop) => (next, none)
  | _ => (machine, none)
termination_by readMeasure machine
decreasing_by
  have := bodyStep_decreases machine state
  simp_all [readMeasure_readBody machine _hs]

/--
Pulls at most one body chunk from the reader: it reads body framing until it produces a chunk, or
returns `none` when it has to wait for input, failed, or the body cannot be pulled (`canPullBody`).
-/
@[inline]
def pullBody (machine : Machine dir) : Machine dir × Option PulledChunk :=
  if machine.canPullBody then pullLoop machine else (machine, none)

end Std.Http.Protocol.H1.Machine
