/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.Http.Data
public import Std.Internal.Http.Internal
public import Std.Internal.Http.Protocol.H1.Parser
public import Std.Internal.Http.Protocol.H1.Config
public import Std.Internal.Http.Protocol.H1.Message
public import Std.Internal.Http.Protocol.H1.Reader
public import Std.Internal.Http.Protocol.H1.Writer
public import Std.Internal.Http.Protocol.H1.Event

public section

/-!
# HTTP/1.1 Protocol State Machine

This module implements the core HTTP/1.1 protocol state machine that handles
parsing requests/responses and generating output. The machine is direction-aware,
supporting both server mode (receiving requests) and client mode (receiving responses).
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std Internal Parsec ByteArray
open Internal

/--
Results from a single step of the state machine.
-/
structure StepResult (dir : Direction) where

  /--
  Events that occurred during this step (e.g., headers received, control flow, errors).
  -/
  events : Array (Event dir) := #[]

  /--
  Output data ready to be sent to the socket.
  -/
  output : ChunkedBuffer := .empty

/--
A single body chunk produced by a pull-driven read.
-/
structure PulledChunk where

  /--
  Whether this chunk finishes the current body stream.
  -/
  final : Bool

  /--
  Whether the chunk data is partial for the current frame/body slice
  (more bytes are still required to complete it).
  -/
  incomplete : Bool

  /--
  The pulled body chunk.
  -/
  chunk : Chunk

/--
The HTTP/1.1 protocol state machine.
-/
structure Machine (dir : Direction) where

  /--
  The state of the reader.
  -/
  reader : Reader dir := {}

  /--
  The state of the writer.
  -/
  writer : Writer dir := {}

  /--
  The configuration.
  -/
  config : Config

  /--
  Events that happened during reading and writing.
  -/
  events : Array (Event dir) := #[]

  /--
  Error thrown by the machine.
  -/
  error : Option Error := none

  /--
  The timestamp for the `Date` header.
  -/
  instant : Option (Std.Time.DateTime .UTC) := none

  /--
  If the connection will be kept alive after the message.
  -/
  keepAlive : Bool := config.enableKeepAlive

  /--
  Whether a forced flush has been requested by the user.
  -/
  forcedFlush : Bool := false

  /--
  Set when a previous `pullBody` call could not make progress in `.readBody`.
  Cleared on new input or state reset.
  -/
  pullBodyStalled : Bool := false

namespace Machine

/--
Applies an update function to the writer sub-state while preserving all other
machine fields.
-/
@[inline]
private def modifyWriter (machine : Machine dir) (fn : Writer dir → Writer dir) : Machine dir :=
  { machine with writer := fn machine.writer }

/--
Applies an update function to the reader sub-state while preserving all other
machine fields.
-/
@[inline]
private def modifyReader (machine : Machine dir) (fn : Reader dir → Reader dir) : Machine dir :=
  { machine with reader := fn machine.reader }

/--
Replaces only the reader state variant (`needHeader`, `readBody`, `failed`, ...)
without touching buffered input or parsed message metadata.
-/
@[inline]
private def setReaderState (machine : Machine dir) (state : Reader.State dir) : Machine dir :=
  machine.modifyReader ({ · with state })

/--
Replaces only the writer state variant while preserving pending user/output data.
-/
@[inline]
private def setWriterState (machine : Machine dir) (state : Writer.State) : Machine dir :=
  machine.modifyWriter ({ · with state })

/--
Appends one event to the machine's event queue for later retrieval by `step`.
-/
@[inline]
private def addEvent (machine : Machine dir) (event : Event dir) : Machine dir :=
  { machine with events := machine.events.push event }

/--
Conditionally enqueues an event when present (`some`), otherwise leaves events
unchanged.
-/
@[inline]
private def setEvent (machine : Machine dir) (event : Option (Event dir)) : Machine dir :=
  match event with
  | some event => machine.addEvent event
  | none => machine

/--
Stores the machine-level error field used by external callers for diagnostics.
-/
@[inline]
private def setError (machine : Machine dir) (error : Error) : Machine dir :=
  { machine with error := some error }

/--
Turns off keep-alive for the current connection; once disabled it remains
disabled for this machine instance.
-/
@[inline]
private def disableKeepAlive (machine : Machine dir) : Machine dir :=
  { machine with keepAlive := false }

/--
Transitions the reader into `.failed`, records an error, and emits a `.failed`
event in one operation.
-/
@[inline]
private def setFailure (machine : Machine dir) (error : H1.Error) : Machine dir :=
  machine
  |>.addEvent (.failed error)
  |>.setReaderState (.failed error)
  |>.setError error

/--
Convenience helper for the common malformed-message failure path.
-/
@[inline]
private def failBadMessage (machine : Machine dir) : Machine dir :=
  machine.setFailure .badMessage

/--
Monotonic keep-alive update: once `keepAlive` is false it never flips back.
-/
@[inline]
private def updateKeepAlive (machine : Machine dir) (should : Bool) : Machine dir :=
  { machine with keepAlive := machine.keepAlive ∧ should }

private inductive BodyMode where
  | fixed (n : Nat)
  | chunked
  | eof

/--
Returns `true` when RFC semantics forbid a response payload body on the wire.
This includes informational responses, `204`, and `304`.
-/
@[inline]
private def responseMustNotHaveBody (status : Status) : Bool :=
  let code := status.toCode.toNat
  (100 ≤ code ∧ code < 200) ∨ code = 204 ∨ code = 304

/--
Checks that request-target form and method are compatible
(`CONNECT` requires authority-form and other methods must not use it).
-/
@[inline]
private def isValidRequestTargetForMethod (message : Message.Head .receiving) : Bool :=
  match message.method, message.uri with
  | .connect, .authorityForm _ => true
  | .connect, _ => false
  | _, .authorityForm _ => false
  | _, _ => true

/--
Validates the required `Host` header for HTTP/1.1 requests:
exactly one value and syntactically valid host syntax.
-/
@[inline]
private def hasSingleValidHostHeader (message : Message.Head .receiving) : Bool :=
  match message.headers.getAll? Header.Name.host with
  | some headers =>
      if headers.size = 1 then
        let hostValue := headers[0]!
        match (Std.Http.URI.Parser.parseHostHeader <* eof).run hostValue.value.toUTF8 with
        | .ok _ => true
        | .error _ => false
      else
        false
  | none => false

/--
Validates an incoming request head and selects the body framing mode.
-/
private def checkReceivingMessageHead (message : Message.Head .receiving) : Option BodyMode := do
  guard (isValidRequestTargetForMethod message)
  guard (hasSingleValidHostHeader message)
  match (← message.getSize true) with
  | .fixed n => return .fixed n
  | .chunked => return .chunked

/--
Validates an incoming response head and selects body framing mode.

For status codes that must not carry a response body, framing headers are still
syntactically validated but the machine always uses `.fixed 0` framing.
-/
private def checkSendingMessageHead (message : Message.Head .sending) : Option BodyMode :=
  let framingInHeaders :=
    message.headers.contains Header.Name.contentLength ∨
    message.headers.contains Header.Name.transferEncoding
  let parsedSize := message.getSize false
  if responseMustNotHaveBody message.status then
    match parsedSize with
    | some _ => some (.fixed 0)
    | none => if framingInHeaders then none else some (.fixed 0)
  else
    match parsedSize with
    | some (.fixed n) => some (.fixed n)
    | some .chunked => some .chunked
    | none => if framingInHeaders then none else some .eof

/--
Direction-dispatched message-head validation.
-/
private def checkMessageHead (message : Message.Head dir) : Option BodyMode := do
  match dir, message with
  | .receiving, message => checkReceivingMessageHead message
  | .sending, message => checkSendingMessageHead message

/--
Returns `true` when an `Expect` header includes `100-continue`.
-/
@[inline]
private def hasExpectContinue (message : Message.Head dir) : Bool :=
  match message.headers.getAll? Header.Name.expect with
  | none => false
  | some values =>
      values.any fun value =>
        value.value.split (· == ',')
        |>.any (fun token => token.trimAscii.toString.toLower == "100-continue")

/--
Returns `true` when user-provided headers include body framing fields.
-/
@[inline]
private def hasFramingHeaders (message : Message.Head dir) : Bool :=
  message.headers.contains Header.Name.contentLength ∨
  message.headers.contains Header.Name.transferEncoding

/--
Builds canonical framing headers for a chosen transfer mode.
The caller handles status/method exceptions that should skip normalization.
-/
@[inline]
private def normalizeFramingHeaders (headers : Headers) (size : Body.Length) : Headers :=
  let headers := headers.erase Header.Name.contentLength |>.erase Header.Name.transferEncoding
  match size with
  | .fixed n => headers.insert Header.Name.contentLength (.ofString! <| toString n)
  | .chunked => headers.insert Header.Name.transferEncoding Header.Value.chunked

/--
Returns `true` when response status forbids framing headers entirely
(informational and `204` responses).
-/
@[inline]
private def responseForbidsFramingHeaders (status : Status) : Bool :=
  let code := status.toCode.toNat
  (100 ≤ code ∧ code < 200) ∨ code = 204

/--
Returns `true` when body chunks should be drained internally rather than surfaced to the caller.
-/
@[inline]
private def shouldIgnoreBodyPull (machine : Machine dir) : Bool :=
  match dir with
  | .receiving => machine.writer.sentMessage
  | .sending => false

/--
Builds the externally exposed `PulledChunk` value from parsed body bytes.

When body consumption is currently internal-only (e.g. request body being
drained after a response was already sent), returns `none`.
-/
@[inline]
private def mkPulledChunk? (machine : Machine dir)
    (final : Bool)
    (incomplete : Bool)
    (extensions : Array (ExtensionName × Option String))
    (data : ByteSlice) : Option PulledChunk :=
  if shouldIgnoreBodyPull machine then
    none
  else
    some {
      final
      incomplete
      chunk := {
        data := ByteSlice.toByteArray data
        extensions := extensions
      }
    }

/--
Checks whether adding `extra` bytes would exceed configured per-message body
limits.
-/
@[inline]
private def fitsBodyLimit (machine : Machine dir) (extra : Nat) : Bool :=
  machine.reader.bodyBytesRead + extra ≤ machine.config.maxBodySize

/--
Accumulates successfully accepted body bytes into the reader accounting.
-/
@[inline]
private def addBodyBytes (machine : Machine dir) (bytes : Nat) : Machine dir :=
  machine.modifyReader (Reader.addBodyBytes bytes)

-- State Checks

/--
Returns `true` if the reader is in a failed state.
-/
@[inline]
def failed (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .failed _ => true
  | _ => false

/--
Returns `true` if the reader has completed successfully.
-/
@[inline]
def isReaderComplete (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .complete => true
  | _ => false

/--
Returns `true` if the reader is closed.
-/
@[inline]
def isReaderClosed (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .closed => true
  | _ => false

/--
Returns `true` if the machine should flush buffered output.
-/
@[inline]
def shouldFlush (machine : Machine dir) : Bool :=
  machine.failed ∨
  machine.reader.state == .closed ∨
  machine.writer.isReadyToSend ∨
  machine.writer.knownSize.isSome ∨
  -- Flush as soon as body bytes exist so keep-alive streaming does not wait
  -- for producer EOF before sending first chunks.
  machine.writer.userData.size > 0

/--
Returns `true` if the writer is waiting for headers of a new message.
-/
@[inline]
def isWaitingMessage (machine : Machine dir) : Bool :=
  machine.writer.state == .waitingHeaders ∧
  ¬machine.writer.sentMessage

/--
Returns `true` if both reader and writer are closed and no output remains.
-/
@[inline]
def halted (machine : Machine dir) : Bool :=
  match machine.reader.state, machine.writer.state with
  | .closed, .closed => machine.writer.outputData.isEmpty
  | _, _ => false

/--
Returns `true` when `pullBody` can attempt to produce body data immediately.
-/
@[inline]
def canPullBody (machine : Machine dir) : Bool :=
  !shouldIgnoreBodyPull machine &&
  match machine.reader.state with
  | .readBody _ => true
  | _ => false

/--
Returns `true` when `pullBody` is currently expected to make progress.
-/
@[inline]
def canPullBodyNow (machine : Machine dir) : Bool :=
  machine.canPullBody && !machine.pullBodyStalled

/--
Runs a parser against reader input and translates parser outcomes into machine
state transitions.

- On success, advances reader input.
- On EOF with open input, emits `needMoreData`.
- On EOF after `noMoreInput`, fails with `connectionClosed`.
- On hard parse errors or size-limit breaches, fails with `badMessage`.
-/
private def parseWith (machine : Machine dir) (parser : Parser α) (limit : Option Nat)
    (expect : Option Nat := none) : Machine dir × Option α :=
  let remaining := machine.reader.input.remainingBytes
  match parser machine.reader.input with
  | .success buffer result =>
      let usedBytes := remaining - buffer.remainingBytes
      if let some limit := limit then
        if usedBytes > limit then
          (machine.setFailure .badMessage, none)
        else
          ({ machine with reader := machine.reader.setInput buffer }, some result)
      else
        ({ machine with reader := machine.reader.setInput buffer }, some result)
  | .error it .eof =>
      let usedBytesUntilFailure := remaining - it.remainingBytes
      if machine.reader.noMoreInput then
        (machine.setFailure .connectionClosed, none)
      else if let some limit := limit then
        if usedBytesUntilFailure ≥ limit
          then (machine.setFailure .badMessage, none)
          else (machine.addEvent (.needMoreData expect), none)
      else
        (machine.addEvent (.needMoreData expect), none)
  | .error _ _ =>
      (machine.setFailure .badMessage, none)

-- Message Processing

/--
Resets per-message reader/writer state for the next pipelined message when
keep-alive remains enabled.

Unconsumed input and already-produced output are preserved. If keep-alive is
disabled, closes reader/writer and emits `.close` instead.
-/
private def resetForNextMessage (machine : Machine ty) : Machine ty :=

  if machine.keepAlive then
    { machine with
      reader := {
        state := .needStartLine,
        input := machine.reader.input,
        messageHead := {},
        messageCount := machine.reader.messageCount + 1,
        bodyBytesRead := 0
      },
      writer := {
        userData := .empty,
        outputData := machine.writer.outputData,
        state := .pending,
        knownSize := none,
        messageHead := {},
        userClosedBody := false,
        sentMessage := false,
        omitBody := false
      },
      events := machine.events.push .next,
      error := none,
      pullBodyStalled := false
    }
  else
    machine.addEvent .close
    |>.setWriterState .closed
    |>.setReaderState .closed

/--
Checks whether the initial framing mode already exceeds `maxBodySize` before any
body bytes are read.
-/
@[inline]
private def exceedsBodyLimitForMode (machine : Machine dir) (mode : BodyMode) : Bool :=
  match mode with
  | .fixed n => n > machine.config.maxBodySize
  | .chunked => false
  | .eof => false

/--
Converts a validated `BodyMode` into the concrete reader state to enter next.

For EOF-delimited bodies this also disables keep-alive since the message
boundary depends on socket close.
-/
private def readerStateForMode (machine : Machine dir) (mode : BodyMode) : Machine dir × Reader.State dir :=
  match mode with
  | .fixed n => (machine, Reader.State.readBody (.fixed n))
  | .chunked => (machine, Reader.State.readBody .chunkedSize)
  | .eof => (machine.disableKeepAlive, Reader.State.readBody .closeDelimited)

/--
Returns whether the machine should pause after headers waiting for a
`canContinue` decision (`Expect: 100-continue` flow).
-/
@[inline]
private def waitingContinueAfterHeaders (machine : Machine dir) : Bool :=
  match dir with
  | .receiving => hasExpectContinue machine.reader.messageHead
  | .sending => false

/--
Completes header-phase transition by emitting header/control events, updating
reader/writer states, and requesting an application answer.
-/
private def advanceAfterHeaders (machine : Machine dir) (state : Reader.State dir) : Machine dir :=
  let waitingContinue := waitingContinueAfterHeaders machine
  let nextState : Reader.State dir := if waitingContinue then Reader.State.«continue» state else state
  let machine := machine.addEvent (.endHeaders machine.reader.messageHead)
  let machine := if waitingContinue then machine.addEvent .continue else machine
  machine
  |>.setReaderState nextState
  |>.setWriterState .waitingHeaders
  |>.addEvent .needAnswer

/--
Processes a finished header block:
1. updates keep-alive policy from config and headers,
2. validates semantic message framing,
3. enforces configured body-size limits,
4. transitions into body/continue state and emits follow-up events.
-/
private def processHeaders (machine : Machine dir) : Machine dir :=
  let machine := machine.updateKeepAlive (machine.reader.messageCount + 1 < machine.config.maxMessages)
  let machine := machine.updateKeepAlive machine.reader.messageHead.shouldKeepAlive

  match checkMessageHead machine.reader.messageHead with
  | none => machine.setFailure .badMessage
  | some mode =>
      if exceedsBodyLimitForMode machine mode then
        machine.setFailure .entityTooLarge
      else
        let (machine, state) := readerStateForMode machine mode
        advanceAfterHeaders machine state

/--
Finalizes and serializes the outgoing start-line + headers.

This applies connection/identity defaults, enforces framing-header
normalization rules based on status semantics, then appends encoded bytes to
writer output and enters `.writingBody`.
-/
private def writeHead (messageHead : Message.Head dir.swap) (machine : Machine dir) : Machine dir :=
  let machine := machine.updateKeepAlive (machine.reader.messageCount + 1 < machine.config.maxMessages)

  let shouldKeepAlive := messageHead.shouldKeepAlive
  let machine := machine.updateKeepAlive shouldKeepAlive
  let size := Writer.determineTransferMode machine.writer

  let headers := messageHead.headers

  -- Add identity header based on direction
  let headers :=
    let identityOpt := machine.config.identityHeader
    match dir, identityOpt with
    | .receiving, some server => headers.insert Header.Name.server server
    | .sending, some userAgent => headers.insert Header.Name.userAgent userAgent
    | _, none => headers

  -- Add Connection: close if needed
  let headers :=
    if !machine.keepAlive ∧ !headers.hasEntry Header.Name.connection Header.Value.close then
      headers.insert Header.Name.connection Header.Value.close
    else
      headers

  -- Normalize framing headers, except for bodyless status codes where framing
  -- metadata is constrained by RFC semantics.
  let headers :=
    match dir, messageHead with
    | .receiving, messageHead =>
        if responseForbidsFramingHeaders messageHead.status then
          headers.erase Header.Name.contentLength |>.erase Header.Name.transferEncoding
        else if messageHead.status == .notModified then
          -- `304` carries no body; keep explicit Content-Length metadata if the
          -- user supplied it, but never keep Transfer-Encoding.
          headers.erase Header.Name.transferEncoding
        else
          normalizeFramingHeaders headers size
    | .sending, _ =>
        normalizeFramingHeaders headers size

  let state := Writer.State.writingBody size

  machine.modifyWriter (fun writer => {
    writer with

    outputData :=
      match dir, messageHead with
      | .receiving, messageHead => Encode.encode (v := .v11) writer.outputData { messageHead with headers }
      | .sending, messageHead => Encode.encode  (v := .v11) writer.outputData { messageHead with headers },

    state
  })

/--
Feeds input bytes into the reader side of the machine.
-/
@[inline]
def feed (machine : Machine ty) (data : ByteArray) : Machine ty :=
  if machine.isReaderClosed then
    machine
  else
    { machine with reader := machine.reader.feed data, pullBodyStalled := false }

/--
Signals that the reader will not receive any more input bytes.
-/
@[inline]
def closeReader (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with noMoreInput := true })

/--
Signals that the writer cannot send more messages because the socket closed.
-/
@[inline]
def closeWriter (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with state := .closed, userClosedBody := true })

/--
Signals that the user is not sending data anymore.
-/
@[inline]
def userClosedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userClosedBody := true })

/--
Signals that the socket is not sending data anymore.
-/
@[inline]
def noMoreInput (machine : Machine dir) : Machine dir :=
  { machine.modifyReader ({ · with noMoreInput := true }) with pullBodyStalled := false }

/--
Set a known size for the message body, replacing any previous value.
-/
@[inline]
def setKnownSize (machine : Machine dir) (size : Body.Length) : Machine dir :=
  machine.modifyWriter (fun w => { w with knownSize := some size })

/--
Suppresses writing body bytes for the current outgoing message while keeping
header generation active. Used for responses that must not carry payload bytes.
-/
@[inline]
def suppressOutgoingBody (machine : Machine dir) (forceZero : Bool := false) : Machine dir :=
  machine.modifyWriter fun w =>
    let knownSize :=
      if forceZero then
        some (.fixed 0)
      else
        w.knownSize
    { w with omitBody := true, userClosedBody := true, knownSize, userData := #[] }

/--
Rejects user-provided framing headers when framing must come from machine state.
-/
@[inline]
private def failOnFramingHeaders (machine : Machine dir) (framingInHeaders : Bool) : Machine dir :=
  if framingInHeaders then
    failBadMessage machine
  else
    machine

/--
Reconciles explicit machine framing (`knownSize`) with user-provided framing
headers from `send` and rejects contradictory inputs.
-/
private def reconcileOutgoingFraming (machine : Machine dir)
    (headerSize : Option Body.Length) (framingInHeaders : Bool) : Machine dir :=
  match machine.writer.knownSize, headerSize with
  | some explicit, some parsed =>
      if explicit == parsed then machine else failBadMessage machine
  | some _, none =>
      failOnFramingHeaders machine framingInHeaders
  | none, some parsed =>
      machine.setKnownSize parsed
  | none, none =>
      failOnFramingHeaders machine framingInHeaders

/--
Marks outgoing bodies as omitted when response semantics (or HEAD method) require
header-only responses.
-/
private def maybeSuppressOutgoingBody (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  match dir, machine, message with
  | .receiving, machine, message =>
      let suppressByStatus := responseMustNotHaveBody message.status
      let suppressByMethod := machine.reader.messageHead.method == .head
      let forceZero := responseForbidsFramingHeaders message.status
      if suppressByStatus ∨ suppressByMethod then
        machine.suppressOutgoingBody (forceZero := forceZero)
      else
        machine
  | .sending, machine, _ =>
      machine

/--
Send the head of a message to the machine.
-/
@[inline]
def send (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  if machine.isWaitingMessage then
    let hadFailure := machine.failed
    let machine := machine.modifyWriter ({ · with messageHead := message, sentMessage := true })
    let framingInHeaders := hasFramingHeaders message
    let headerSize := message.getSize false

    let machine := reconcileOutgoingFraming machine headerSize framingInHeaders
    let machine := maybeSuppressOutgoingBody machine message

    if machine.failed && !hadFailure then
      machine
    else
      machine.setWriterState .waitingForFlush
  else
    machine

/--
Allows body processing to continue after receiving `Expect: 100-continue`.
-/
def canContinue (machine : Machine dir) (status : Status) : Machine dir :=
  match dir, machine.reader.state with
  | .sending, _ => machine
  | .receiving, Reader.State.«continue» nextState =>
      if status == .«continue» then
        let machine := machine.modifyWriter (fun writer => {
          writer with outputData := Encode.encode (v := .v11) writer.outputData ({ status := .«continue» } : Response.Head)
        })
        machine.setReaderState nextState
      else
        machine.send { status }
        |>.setKnownSize (.fixed 0)
        |>.userClosedBody
        |>.disableKeepAlive
        |>.closeReader
        |>.setReaderState .closed
  | .receiving, _ => machine

/-- Sends data to the socket. -/
@[inline]
def sendData (machine : Machine dir) (data : Array Chunk) : Machine dir :=
  if data.isEmpty then
    machine
  else
    machine.modifyWriter (fun writer => { writer with userData := writer.userData ++ data })

/-- Gets all events of the machine. -/
@[inline]
def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/-- Takes all accumulated output to send to the socket. -/
@[inline]
def takeOutput (machine : Machine dir) : Machine dir × ChunkedBuffer :=
  let output := machine.writer.outputData
  ({ machine with writer := { machine.writer with outputData := .empty } }, output)

/--
For writer-side protocol violations (e.g. fixed-length overflow), force
connection shutdown and surface a close event.
-/
@[inline]
private def closeOnBadMessage (machine : Machine dir) : Machine dir :=
  machine
  |>.setError .badMessage
  |>.disableKeepAlive
  |>.closeWriter
  |>.closeReader
  |>.setReaderState .closed
  |>.addEvent .close

/--
Returns total payload bytes currently buffered in `writer.userData`.
-/
@[inline]
private def bufferedUserDataBytes (writer : Writer dir) : Nat :=
  writer.userData.foldl (fun acc chunk => acc + chunk.data.size) 0

/--
Handles transitions after a writer message completes.

Depending on reader state and keep-alive, this either resets for next message
or closes the writer/connection.
-/
private def processCompleteStep (machine : Machine dir) : Machine dir :=
  if machine.isReaderComplete then
    if machine.keepAlive then
      resetForNextMessage machine
    else
      machine.setWriterState .closed
      |>.addEvent .close
  else if machine.isReaderClosed then
    machine.setWriterState .closed
    |>.addEvent .close
  else if machine.keepAlive then
    machine
  else
    machine.setWriterState .closed

mutual

/--
Marks writer message as complete and continues the writer state machine to apply
post-completion transitions.
-/
@[inline]
private partial def completeWriterMessage (machine : Machine dir) : Machine dir :=
  machine.setWriterState .complete
  |> processWrite

/--
Completes a message whose body is intentionally omitted from wire output
(`HEAD`/bodyless status handling).
-/
@[inline]
private partial def completeOmittedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userData := #[] })
  |> completeWriterMessage

/--
Processes a fixed-size body when remaining size is zero.

Accepts completion only when producer has closed and no extra bytes are queued;
otherwise treats queued bytes as protocol error.
-/
@[inline]
private partial def processFixedZeroBody (machine : Machine dir) : Machine dir :=
  if machine.writer.userData.isEmpty then
    if machine.writer.userClosedBody then
      completeWriterMessage machine
    else
      machine
  else
    closeOnBadMessage machine

/--
Processes fixed-length body data when buffered user bytes are present.

Enforces exact-length semantics (no overflow), writes up to remaining length,
and updates writer state for any bytes still pending.
-/
private partial def processFixedBufferedBody (machine : Machine dir) (n : Nat) : Machine dir :=
  let writer := machine.writer
  let bufferedBytes := bufferedUserDataBytes writer
  if bufferedBytes > n then
    -- More bytes than declared fixed length. Close the connection instead of
    -- silently truncating and presenting a complete payload to the peer.
    closeOnBadMessage machine
  else if bufferedBytes = n ∧ !writer.userClosedBody then
    -- Do not flush the final fixed-length bytes until the producer closes.
    -- This lets us detect late overflow chunks as protocol violations.
    machine
  else
    let (writer, remaining) := Writer.writeFixedBody writer n
    let machine := { machine with writer }
    let writer := machine.writer
    if remaining = 0 then
      if writer.userData.isEmpty then
        if writer.userClosedBody then
          completeWriterMessage machine
        else
          machine.setWriterState (.writingBody (.fixed 0))
      else
        closeOnBadMessage machine
    else
      machine.setWriterState (.writingBody (.fixed remaining))

/--
Handles fixed-length writer state when no user bytes are currently buffered.

If producer closed early, the message is invalid and the connection closes.
-/
@[inline]
private partial def processFixedIdleBody (machine : Machine dir) : Machine dir :=
  if machine.writer.userClosedBody then
    machine
    |>.disableKeepAlive
    |>.setWriterState .closed
    |>.addEvent .close
  else
    machine

/--
Dispatch for fixed-length body writing, including omitted-body fast path and
zero/non-zero remaining-length handling.
-/
@[inline]
private partial def processFixedBody (machine : Machine dir) (n : Nat) : Machine dir :=
  if machine.writer.omitBody then
    completeOmittedBody machine
  else if n = 0 then
    processFixedZeroBody machine
  else if machine.writer.userData.size > 0 then
    processFixedBufferedBody machine n
  else
    processFixedIdleBody machine

/--
Processes chunked transfer-encoding output.

Writes buffered chunks when available, writes terminal `0\\r\\n\\r\\n` on
producer close, and supports omitted-body completion.
-/
private partial def processChunkedBody (machine : Machine dir) : Machine dir :=
  if machine.writer.omitBody then
    completeOmittedBody machine
  else if machine.writer.userClosedBody then
    machine.modifyWriter Writer.writeFinalChunk
    |> completeWriterMessage
  else if machine.writer.userData.size > 0 ∨ machine.writer.isReadyToSend then
    machine.modifyWriter Writer.writeChunkedBody
    |> processWrite
  else
    machine

/--
Advances writer-side state machine by one logical transition.

Depending on writer state, this may:
- request an application answer,
- serialize headers,
- flush fixed/chunked body bytes,
- finalize/close after completion.
-/
partial def processWrite (machine : Machine dir) : Machine dir :=
  match machine.writer.state with
  | .pending =>
      if machine.reader.isClosed then machine.closeWriter else machine
  | .waitingHeaders =>
      machine.addEvent .needAnswer
  | .waitingForFlush =>
      if machine.shouldFlush then
        machine.writeHead machine.writer.messageHead
        |> processWrite
      else
        machine
  | .writingHeaders =>
      machine.setWriterState (.writingBody (Writer.determineTransferMode machine.writer))
      |> processWrite
  | .writingBody (.fixed n) =>
      processFixedBody machine n
  | .writingBody .chunked =>
      processChunkedBody machine
  | .shuttingDown =>
      if machine.writer.outputData.isEmpty then
        machine.setWriterState .complete
        |> processWrite
      else
        machine
  | .complete =>
      processCompleteStep machine
  | .closed =>
      machine

end

/-- Maps a reader failure to an HTTP status code. -/
private def errorResponseStatus (error : H1.Error) : Status :=
  match error with
  | .unsupportedVersion => .httpVersionNotSupported
  | .entityTooLarge => .payloadTooLarge
  | .unsupportedMethod => .notImplemented
  | _ => .badRequest

/--
Handles reader failure state.

On server-side (`.receiving`), it opportunistically emits one error response if
no response head has been sent yet, then closes reader state and records the
failure event/error.
-/
private def handleReaderFailed (machine : Machine dir) (error : H1.Error) : Machine dir :=
  let machine : Machine dir :=
    match dir with
    | .receiving =>
      if ¬machine.writer.sentMessage ∧ ¬machine.writer.isClosed then
        machine
       |>.setWriterState .waitingHeaders
       |>.disableKeepAlive
       |>.send { status := errorResponseStatus error }
       |>.userClosedBody
      else
        machine
    | .sending => machine

  machine
  |>.setReaderState .closed
  |>.addEvent (.failed error)
  |>.setError error

/--
Utility result for body parser branches that could not make progress this step.
-/
@[inline]
private def bodyNoProgress (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  (machine, none, false)

/--
Utility result for body parser branches that exceed configured body limits.
-/
@[inline]
private def bodyTooLarge (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  (machine.setFailure .entityTooLarge, none, false)

/--
Common body-chunk emission helper.

Updates size accounting and reader state, optionally emits `.closeBody`, and
returns an optional pulled chunk (suppressed when body is being internally
drained).
-/
private def emitBodyChunk (machine : Machine dir)
    (nextState : Reader.State dir)
    (final : Bool)
    (incomplete : Bool)
    (extensions : Array (ExtensionName × Option String))
    (data : ByteSlice)
    (closeBody : Bool := false) :
    Machine dir × Option PulledChunk × Bool :=
  let bodySize := data.size
  if !fitsBodyLimit machine bodySize then
    bodyTooLarge machine
  else
    let machine := machine
      |>.addBodyBytes bodySize
      |>.setReaderState nextState
    let machine := if closeBody then machine.addEvent .closeBody else machine
    (machine, mkPulledChunk? machine final incomplete extensions data, true)

/--
Consumes a zero-length fixed body and immediately marks body completion.
-/
private def parseFixedZeroBody (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  emitBodyChunk machine .complete true false #[] .empty (closeBody := true)

/--
Consumes fixed-length body bytes, yielding complete or partial segments.
-/
private def parseFixedBody (machine : Machine dir) (size : Nat) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine (parseFixedSizeData size) (limit := none) (some size)
  match result with
  | some (.complete body) =>
      emitBodyChunk machine .complete true false #[] body (closeBody := true)
  | some (.incomplete body remaining) =>
      -- In fixed-length framing this is a partial body segment, not a chunked-frame fragment.
      emitBodyChunk machine (.readBody (.fixed remaining)) false false #[] body
  | none =>
      bodyNoProgress machine

/--
Parses next chunk-size line in chunked mode and transitions to chunk-data state.
-/
private def parseChunkSizeBody (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine
    (parseChunkSize machine.config)
    (limit := some machine.config.maxChunkLineLength)
  match result with
  | some (size, ext) =>
      if size > machine.config.maxChunkSize then
        bodyTooLarge machine
      else if !fitsBodyLimit machine size then
        bodyTooLarge machine
      else
        (machine.setReaderState (.readBody (.chunkedBody ext size)), none, true)
  | none =>
      bodyNoProgress machine

/--
Parses trailers after a zero-size chunk and finalizes chunked body processing.
-/
private def parseLastChunkBodyState (machine : Machine dir)
    (ext : Array (ExtensionName × Option String)) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine (parseLastChunkBody machine.config) (limit := none)
  match result with
  | some _ =>
      emitBodyChunk machine .complete true false ext .empty (closeBody := true)
  | none =>
      bodyNoProgress machine

/--
Consumes chunk-data bytes for the current chunk, handling complete and partial
chunk payload reads.
-/
private def parseChunkedBodyState (machine : Machine dir)
    (ext : Array (ExtensionName × Option String))
    (size : Nat) :
    Machine dir × Option PulledChunk × Bool :=
  let (machine, result) := parseWith machine (parseChunkSizedData size) (limit := none) (some size)
  match result with
  | some (.complete body) =>
      emitBodyChunk machine (.readBody .chunkedSize) false false ext body
  | some (.incomplete body remaining) =>
      emitBodyChunk machine (.readBody (.chunkedBody ext remaining)) false true ext body
  | none =>
      bodyNoProgress machine

/--
Consumes close-delimited body bytes.

When socket EOF is observed (`noMoreInput` + atEnd), closes body; otherwise it
either emits available bytes or requests more data.
-/
private def parseCloseDelimitedBody (machine : Machine dir) :
    Machine dir × Option PulledChunk × Bool :=
  let reader := machine.reader
  if reader.input.atEnd then
    if reader.noMoreInput then
      emitBodyChunk machine .complete true false #[] .empty (closeBody := true)
    else
      bodyNoProgress (machine.addEvent (.needMoreData none))
  else
    let data := reader.input.array[reader.input.pos...reader.input.array.size]
    let machine := machine.modifyReader (fun r => r.advance r.remainingBytes)
    emitBodyChunk machine (.readBody .closeDelimited) false false #[] data

/--
Dispatches body parsing according to current reader body-framing sub-state.
-/
private def parseBody (machine : Machine dir) (bodyState : Reader.BodyState) :
    Machine dir × Option PulledChunk × Bool :=
  match bodyState with
  | .fixed 0 =>
      parseFixedZeroBody machine
  | .fixed size =>
      parseFixedBody machine size
  | .chunkedSize =>
      parseChunkSizeBody machine
  | .chunkedBody ext 0 =>
      parseLastChunkBodyState machine ext
  | .chunkedBody ext size =>
      parseChunkedBodyState machine ext size
  | .closeDelimited =>
      parseCloseDelimitedBody machine

/--
Converts raw parsed header name/value strings into typed header representations.
-/
@[inline]
private def typedHeader? (name : String) (value : String) : Option (Header.Name × Header.Value) :=
  Prod.mk <$> Header.Name.ofString? name <*> Header.Value.ofString? value

mutual

/--
Parses one request start-line in server mode and initializes `reader.messageHead`
for header parsing.

Unsupported methods or versions are converted into protocol failures.
-/
private partial def processReceivingStartLine (machine : Machine .receiving) : Machine .receiving :=
  let (machine, result) := parseWith machine
    (parseRequestLineRawVersion machine.config)
    (limit := some machine.config.maxStartLineLength)

  match result with
  | some (method?, uri, version) =>
      if version == some .v11 then
        if let some method := method? then
          machine
          |>.modifyReader (.setMessageHead ({ method, version := .v11, uri, headers := .empty }))
          |>.setReaderState (.needHeader 0)
          |> processRead
        else
          machine.setFailure .unsupportedMethod
      else
        machine.setFailure .unsupportedVersion
  | none =>
      machine

/--
Parses one response start-line in client mode and initializes
`reader.messageHead` for header parsing.
-/
private partial def processSendingStartLine (machine : Machine .sending) : Machine .sending :=
  let (machine, result) := parseWith machine
    (parseStatusLineRawVersion machine.config)
    (limit := some machine.config.maxStartLineLength)

  match result with
  | some (status, version) =>
      if version == some .v11 then
        machine
        |>.modifyReader (.setMessageHead ({ status, version := .v11, headers := .empty }))
        |>.setReaderState (.needHeader 0)
        |> processRead
      else
        machine.setFailure .unsupportedVersion
  | none =>
      machine

/--
Entry point for `Reader.State.needStartLine`.

Requests more data when input is currently empty, closes on EOF, and otherwise
dispatches to request-line/status-line parsing based on machine direction.
-/
private partial def processNeedStartLine (machine : Machine dir) : Machine dir :=
  let reader := machine.reader
  if reader.noMoreInput ∧ reader.input.atEnd then
    machine.setReaderState .closed
  else if reader.input.atEnd then
    machine.addEvent (.needMoreData none)
  else
    match dir, machine with
    | .receiving, machine => processReceivingStartLine machine
    | .sending, machine => processSendingStartLine machine

/--
Processes a parsed header field line.

Accounts for header byte/count limits, type-checks name/value pairs, appends
header to `reader.messageHead`, and recurses into the next header slot.
-/
private partial def processParsedHeader (machine : Machine dir) (headerCount : Nat)
    (startRemaining : Nat) (name : String) (value : String) : Machine dir :=
  let reader := machine.reader
  let headerBytes := startRemaining - reader.input.remainingBytes

  if headerCount ≥ machine.config.maxHeaders ∨ reader.headerBytesRead + headerBytes > machine.config.maxHeaderBytes then
    failBadMessage machine
  else
    match typedHeader? name value with
    | some (name, headerValue) =>
      machine
      |>.modifyReader (.addHeader name headerValue)
      |>.modifyReader (.addHeaderBytes headerBytes)
      |>.setReaderState (.needHeader (headerCount + 1))
      |> processRead
    | none =>
      failBadMessage machine

/--
Consumes one header line in `needHeader` state.

On a regular field line it delegates to `processParsedHeader`; on an empty line
it finalizes header processing via `processHeaders`.
-/
private partial def processNeedHeader (machine : Machine dir) (headerCount : Nat) : Machine dir :=
  let start := machine.reader.input.remainingBytes
  let (machine, result) := parseWith machine (parseSingleHeader machine.config) (limit := none)
  match result with
  | some (some (name, value)) => processParsedHeader machine headerCount start name value
  | some none => processHeaders machine |> processRead
  | none => machine

/--
Reader-side handling for `.readBody`.

When upper layers are not pulling body chunks, the machine drains body bytes
internally to keep parsing/connection progress moving.
-/
private partial def processReadBodyState (machine : Machine dir) (bodyState : Reader.BodyState) : Machine dir :=
  if shouldIgnoreBodyPull machine then
    let (machine, _pulledChunk, shouldContinue) := parseBody machine bodyState
    if shouldContinue then processRead machine else machine
  else
    machine

/--
Handles `Reader.State.complete` by deciding whether to stay open for the next
message or transition to `.closed`.
-/
private partial def processReaderCompleteState (machine : Machine dir) : Machine dir :=
  let reader := machine.reader
  if (reader.noMoreInput ∧ reader.input.atEnd) ∨ ¬machine.keepAlive then
    machine.setReaderState .closed
  else
    machine

/--
Advances reader-side state machine by one logical transition.

Dispatches parsing work according to current reader state (start-line, headers,
body, completion, or failure handling).
-/
partial def processRead (machine : Machine dir) : Machine dir :=
  match machine.reader.state with
  | .needStartLine =>
      processNeedStartLine machine
  | .needHeader headerCount =>
      processNeedHeader machine headerCount
  | .readBody bodyState =>
      processReadBodyState machine bodyState
  | Reader.State.«continue» _ =>
      machine
  | .complete =>
      processReaderCompleteState machine
  | .closed =>
      machine
  | .failed error =>
      handleReaderFailed machine error

end

/--
Execute one step of the state machine.
-/
def step (machine : Machine dir) : Machine dir × StepResult dir :=
  let machine := machine.processRead.processWrite
  let (machine, events) := machine.takeEvents
  let (machine, output) := machine.takeOutput
  (machine, { events, output })

/--
Internal recursive helper for `pullBody`.

Keeps advancing body parsing until either a chunk is produced or no immediate
progress can be made.
-/
private partial def pullNextChunk (machine : Machine dir) : Machine dir × Option PulledChunk :=
  match machine.reader.state with
  | .readBody bodyState =>
      let (machine, pulledChunk, shouldContinue) := parseBody machine bodyState
      match pulledChunk with
      | some _ =>
          (machine, pulledChunk)
      | none =>
          if shouldContinue then
            pullNextChunk machine
          else
            (machine, none)
  | _ =>
      (machine, none)

/--
Pulls at most one body chunk from the reader.

It advances body parsing until it either:
- produces a chunk (`some PulledChunk`), or
- cannot continue for now (`none`).
-/
@[inline]
def pullBody (machine : Machine dir) : Machine dir × Option PulledChunk :=
  let (machine, pulledChunk) := pullNextChunk machine
  let readerState := machine.reader.state
  let ignoreBodyPull := shouldIgnoreBodyPull machine
  let stalled :=
    pulledChunk.isNone &&
    !ignoreBodyPull &&
    match readerState with
    | .readBody _ => true
    | _ => false
  ({ machine with pullBodyStalled := stalled }, pulledChunk)

end Std.Http.Protocol.H1.Machine
