/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Init
import Std.Internal.Http.Data.Headers
import Std.Internal.Http.Data.Request
import Std.Internal.Http.Data.Response
import Std.Internal.Http.Data.Body
import Std.Internal.Http.V11.Parser

/-!
# HTTP/1.1 State Machine

This module implements a streaming HTTP/1.1 state machine that can handle both request and response
parsing and generation. The machine operates in two modes:

- **Request mode**: Parses incoming HTTP requests and generates responses
- **Response mode**: Parses incoming HTTP responses (useful for client implementations)
-/

open Std.Internal.Parsec.ByteArray (Parser)

namespace Std
namespace Http
namespace V11

set_option linter.all true

/--
Connection limits configuration with validation.
-/
structure Config where
  /--
  Maximum number of requests per connection.
  -/
  maxRequests : Nat := 100

  /--
  Maximum number of headers allowed per request.
  -/
  maxHeaders : Nat := 50

  /--
  Maximum size of a single header value.
  -/
  maxHeaderSize : Nat := 8192

  /--
  Connection timeout in seconds.
  -/
  timeoutSeconds : Nat := 10

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  Whether to enable chunked transfer encoding.
  -/
  enableChunked : Bool := true

  /--
  Size threshold for flushing output buffer.
  -/
  highMark : Nat := 4096

/--
This is the mode that is used by the machine to check the input and output.
-/
inductive Mode
  /--
  Request mode - machine expects to receive HTTP requests
  -/
  | request

  /--
  Response mode - machine expects to receive HTTP responses
  -/
  | response

namespace Mode

/--
Inverts the mode.
-/
def inverse : Mode → Mode
  | .request => .response
  | .response => .request

end Mode

/--
Determines the type of the status line based on the Mode.
-/
abbrev StatusLine : Mode → Type
  | .request => Data.Method × String × Data.Version
  | .response => Data.Version × Data.Status × String

instance : Repr (StatusLine m) where
  reprPrec r s :=
    match m with
    | .request => reprPrec r s
    | .response => reprPrec r s

/--
Determines the type of the status line based on the Mode.
-/
abbrev Message (t : Type) : Mode → Type
  | .request => Data.Request t
  | .response => Data.Response t

instance : ToString (Message t m) where
  toString r :=
    match m with
    | .request => toString r
    | .response => toString r

namespace Message

/--
Extracts headers from a message regardless of mode.
-/
def headers (message : Message t mode) : Data.Headers :=
  match mode with
  | .request => Data.Request.headers message
  | .response => Data.Response.headers message

/--
Adds a header to a message regardless of mode.
-/
def addHeader (message : Message t mode) (k : String) (v : String) : Message t mode :=
  match mode with
  | .request => { message with headers := message.headers.insert k v }
  | .response => { message with headers := message.headers.insert k v }

end Message

/--
Represents the expected size encoding for HTTP message body
-/
inductive Size
  /--
  Fixed size body with known byte count
  -/
  | fixed (n : Nat)

  /--
  Chunked transfer encoding
  -/
  | chunked

deriving Repr, Inhabited

/--
Specific HTTP processing errors with detailed information.
-/
inductive Error where
  /--
  Malformed request line or status line.
  -/
  | invalidStatusLine

  /--
  Invalid or malformed header.
  -/
  | invalidHeader

  /--
  Request timeout occurred.
  -/
  | timeout

  /--
  Request entity too large.
  -/
  | entityTooLarge

  /--
  Unsupported HTTP method.
  -/
  | unsupportedMethod

  /--
  Unsupported HTTP version.
  -/
  | unsupportedVersion

  /--
  Invalid chunk encoding.
  -/
  | invalidChunk

  /--
  Bad request
  -/
  | badRequest
  /--
  Generic error with message.
  -/
  | other (message : String)
deriving Repr, BEq

/--
Creates appropriate error response based on error type.
-/
private def Error.toResponse (error : Error) : Data.Response Data.Body :=
  let (status, body) := match error with
    | .badRequest => (Data.Status.badRequest, none)
    | .invalidStatusLine => (.badRequest, none)
    | .invalidHeader => (.badRequest, none)
    | .timeout => (.requestTimeout, none)
    | .entityTooLarge => (.payloadTooLarge, none)
    | .unsupportedMethod => (.methodNotAllowed, none)
    | .unsupportedVersion => (.httpVersionNotSupported, none)
    | .invalidChunk => (.badRequest, none)
    | .other msg => (.internalServerError, some msg)

  { status := status,
    version := .v11,
    headers := .empty,
    body := body <&> (Data.Body.bytes ∘ ByteSlice.ofByteArray ∘ String.toUTF8) |>.getD .zero }

/--
Events that can occur during HTTP message processing.
-/
inductive Event (mode : Mode)
  /--
  Event received when chunk extension data is encountered in chunked encoding.
  -/
  | chunkExt (ext : ByteSlice)

  /--
  Event received the headers end.
  -/
  | endHeaders (size : Size)

  /--
  Event received when some data arrives from the received thing.
  -/
  | gotData (final : Bool) (data : ByteSlice)

  /--
  Need more data is an event that arrives when the input ended and it requires more
  data to continue
  -/
  | needMoreData

  /--
  Event received when all request data has been parsed and ready to send response.
  -/
  | readyToRespond

  /--
  Event received when it requires more data to continue
  -/
  | awaitingAnswer

  /--
  Event received when parsing or processing fails with an error message.
  -/
  | failed (reason : Error)

  /--
  Event received when connection should be closed.
  -/
  | close

  /--
  Awaiting the next request
  -/
  | next
deriving Repr, Inhabited

/--
State of the `Machine`.
-/
inductive State : Type
  /--
  Initial state waiting for HTTP status line.
  -/
  | needStatusLine : State

  /--
  State waiting for HTTP headers, tracking number of headers parsed.
  -/
  | needHeader : Nat → State

  /--
  State waiting for chunk size in chunked transfer encoding.
  -/
  | needChunkedSize : State

  /--
  State waiting for chunk body data of specified size.
  -/
  | needChunkedBody : Nat → State

  /--
  State waiting for fixed-length body data of specified size.
  -/
  | needFixedBody : Nat → State

  /--
  State when request is fully parsed and ready to generate response.
  -/
  | readyToAnswer : State

  /--
  State when the response can send data.
  -/
  | awaitingAnswer

  /--
  State waiting for connection to close after response sent.
  -/
  | awaitingClose : State

  /--
  Final state when connection is closed.
  -/
  | closed

  /--
  Ready for next request.
  -/
  | next

  /--
  Failed state with error.
  -/
  | failed (error : Error)
deriving Inhabited, Repr, BEq

/--
The state machine that receives some input bytes and outputs bytes for the HTTP 1.1 protocol.
-/
structure Machine (mode : Mode) where

  /--
  The current state of the machine
  -/
  state : State := .needStatusLine

  /--
  The input status line.
  -/
  inputStatusLine : Option (StatusLine mode) := none

  /--
  The input headers.
  -/
  inputHeaders : Data.Headers := .empty

  /--
  The output status line.
  -/
  outputMessage : Option (Message Data.Body mode.inverse) := none

  /--
  The output headers.
  -/
  outputHeaders : Data.Headers := .empty

  /--
  If the headers has been sent.
  -/
  sentOutputHead : Bool := false

  /--
  This is the buffer that we receive from the user
  -/
  inputBuffer : ByteArray.Iterator := (ByteArray.emptyWithCapacity 4096).iter

  /--
  This is the buffer that we are going to output for the user.
  -/
  outputBuffer : ByteArray := .empty

  /--
  Chunked data to send in the future
  -/
  chunkedData : ByteArray := .empty

  /--
  The event that the machine produced.
  -/
  event : Option (Event mode) := some .needMoreData

  /--
  The minimum size of the body
  -/
  size : Option UInt64 := none

  /--
  Machine configuration.
  -/
  config : Config := {}

  /--
  Amount of requests parsed.
  -/
  requestCount : Nat := 0

  /--
  Whether response uses chunked encoding.
  -/
  chunkedAnswer : Bool := false

  /--
  Whether connection should be kept alive.
  -/
  keepAlive : Bool := true

namespace Machine

/--
Result of parsing operation on input buffer
-/
inductive ParseResult (α : Type) where
  /--
  Reached end of input buffer without complete parse
  -/
  | eof

  /--
  Successfully parsed value with remaining buffer
  -/
  | ok (x : α) (b : ByteArray.Iterator)

  /--
  Parse failed with error
  -/
  | err (err : Error)

/--
Sets machine to failed state with specific error.
-/
def setError (machine : Machine mode) (error : Error) : Machine mode :=
  { machine with state := .failed error, event := some (.failed error) }

/--
Sets the event in the machine.
-/
private def addEvent (machine : Machine mode) (event : Event mode) : Machine mode :=
  { machine with event := some event }

/--
Sets the status in the machine.
-/
private def setState (machine : Machine mode) (state : State) : Machine mode :=
  { machine with state }

/--
Common parsing wrapper that handles errors and EOF consistently.
-/
private def parseWith (machine : Machine mode) (parser : Parser α) : (Machine mode × Option α) :=
  match parser machine.inputBuffer with
  | .success buffer reqLine => ({ machine with inputBuffer := buffer }, some reqLine)
  | .error _ .eof =>  (machine.addEvent .needMoreData, none)
  | .error _ _ => (machine.setError .badRequest, none)

/--
Converts raw byte digits to HTTP version.
-/
private def parseVersion (major minor : UInt8) : Option Data.Version :=
  Data.Version.fromNumber? (major.toNat - 48) (minor.toNat - 48)

/--
Validates that HTTP version is supported by machine configuration.
-/
private def validateVersion (version : Data.Version) : Bool :=
  version == .v11

/--
Parses HTTP request line into status line format.
-/
private def parseRequestStatusLine (raw : Parser.RequestLine) : Option (StatusLine .request) := do
  let version ← parseVersion raw.major raw.minor
  guard (validateVersion version)
  let method ← Data.Method.fromString? =<< String.fromUTF8? raw.method.toByteArray
  let uri ← String.fromUTF8? raw.uri.toByteArray
  pure (method, uri, version)

/--
Parses HTTP response status line into status line format.
-/
private def parseResponseStatusLine (raw : Parser.StatusLine) : Option (StatusLine .response) := do
  let version ← parseVersion raw.major raw.minor
  guard (validateVersion version)
  let status ← Data.Status.fromCode? raw.statusCode.toUInt16
  let reason ← String.fromUTF8? raw.reasonPhrase.toByteArray
  pure (version, status, reason)

/--
Common parsing workflow for status lines.
-/
private def parseStatusWith
  (machine : Machine mode)
  (parser : Parser α)
  (transform : α → Option (StatusLine mode))
  : (Machine mode × Option (StatusLine mode)) :=
    let (machine, result) := parseWith machine parser
    if let some result := result then
      (machine, transform result)
    else
      (machine, none)

/--
Parses HTTP status line based on machine mode.
-/
private def parseStatusLine (machine : Machine mode) : (Machine mode × Option (StatusLine mode)) :=
  match mode with
  | .request => parseStatusWith machine Parser.parseRequestLine parseRequestStatusLine
  | .response => parseStatusWith machine Parser.parseStatusLine parseResponseStatusLine

/--
Formats a chunk for chunked transfer encoding.
-/
private def formatChunk (data : ByteArray) : ByteArray :=
  let sizeHex := (Nat.toDigits 16 data.size) |>.toArray |>.map Char.toUInt8 |> ByteArray.mk
  sizeHex ++ "\r\n".toUTF8 ++ data ++ "\r\n".toUTF8

/--
Formats the final chunk for chunked transfer encoding.
-/
private def formatFinalChunk : ByteArray :=
  "0\r\n\r\n".toUTF8

/--
Validates headers and determines body encoding type.
-/
private def validateHeaders (mode : Mode) (headers : Data.Headers) : Option Size := do
  let hostValid : Bool := match mode with
    | .request => headers.get? "host" |>.isSome
    | .response => true

  guard hostValid

  match (headers.getSingle? "Content-Length", headers.get? "Transfer-Encoding") with
  | (some cl, none) => do
    let num ← cl.toNat?
    some (.fixed num)
  | (none, some hs) =>
    if hs.contains "chunked" then
      some .chunked
    else
      some (.fixed 0)
  | (none, none) =>
    some (.fixed 0)
  | _ => none

/--
Resets the machine for a new request on the same connection (keep-alive)
-/
private def reset (machine : Machine mode) : Machine mode :=
  { machine with
    state := .needStatusLine,
    inputStatusLine := none,
    inputHeaders := .empty,
    outputMessage := none,
    outputHeaders := .empty,
    sentOutputHead := false,
    inputBuffer := ByteArray.empty.iter,
    outputBuffer := .empty,
    chunkedData := .empty,
    event := some .needMoreData,
    requestCount := machine.requestCount + 1 }

/--
Checks if the machine is in a terminal state that requires flushing.
-/
private def isTerminalState (machine : Machine mode) : Bool :=
  match machine.state with
  | .closed => true
  | .failed _ => true
  | .next => true
  | _ => false
/--
Checks if output buffer exceeds high water mark and needs flushing.
-/
def needsFlush (machine : Machine mode) : Bool :=
  machine.outputBuffer.size >= machine.config.highMark
  || isTerminalState machine

/--
Modify message headers based on the given size.
-/
private def addSizeHeader (msg : Message t mode) (size : Size) : Message t mode :=
  match size with
  | .chunked => msg.addHeader "Transfer-Encoding" "chunked"
  | .fixed 0 => msg
  | .fixed n => msg.addHeader "Content-Length" (toString n)

/--
Modify message headers based on the given size.
-/
private def isChunked (size : Size) : Bool :=
  match size with
  | .chunked => true
  | .fixed _ => false

/--
Adds the message header to the output buffer if not already sent.
-/
private def sendOutputHead (machine : Machine mode) (size : Size) : Machine mode :=
  if machine.sentOutputHead then
    machine
  else
   match machine.outputMessage with
    | some msg =>
      let outputMessage := addSizeHeader msg size
      { machine with
        outputMessage,
        outputBuffer := machine.outputBuffer ++ (toString outputMessage).toUTF8,
        chunkedAnswer := isChunked size,
        sentOutputHead := true }
    | none => machine

/--
Appends data to output buffer based on encoding type.
-/
def appendToOutputBuffer (machine : Machine mode) (data : ByteArray) (size : Size) : Machine mode :=
  let dataToAppend :=
    match size with
    | .chunked => formatChunk data
    | .fixed _ => data
  { machine with outputBuffer := machine.outputBuffer.append dataToAppend }

/--
Writes data to the output buffer, ensuring the message head is sent first.
-/
def writeToOutputBuffer (machine : Machine mode) (data : ByteArray) (size : Size) : Machine mode :=
  machine
  |>.sendOutputHead size
  |>.appendToOutputBuffer data size

/--
Checks if chunked data should be flushed based on size and force flag.
-/
def shouldFlushChunkedData (machine : Machine mode) (force : Bool) : Bool :=
  force || machine.chunkedData.size >= machine.config.highMark

/--
Writes data to the local buffer. Encoding decision is deferred until flush time.
-/
def writeData (machine : Machine mode) (data : ByteArray) : Machine mode :=
  { machine with chunkedData := machine.chunkedData ++ data }

/--
Flushes the output buffer and returns the data to send.
-/
def flush (machine : Machine mode) (final : Bool := false) : Machine mode × ByteArray :=
  -- Only flush if we hit highMark or it's final
  if machine.chunkedData.size >= machine.config.highMark || final then
    let machine :=
      if !machine.chunkedData.isEmpty then
        if final then
          dbg_trace "ha the size {machine.chunkedData.size}"
          -- Final flush: use Content-Length
          let size := Size.fixed machine.chunkedData.size
          let machine := sendOutputHead machine size
          let machine := appendToOutputBuffer machine machine.chunkedData size
          { machine with chunkedData := .empty }
        else
          -- Non-final flush: use chunked encoding
          dbg_trace "ha the chunk size {machine.chunkedData.size}"
          let machine := sendOutputHead machine Size.chunked
          let machine := appendToOutputBuffer machine machine.chunkedData Size.chunked
          { machine with chunkedData := .empty }
      else if final then
        -- Final flush with no buffered data
          dbg_trace "ha the none size {machine.chunkedData.size}"
        let machine := sendOutputHead machine (Size.fixed 0)
        machine
      else
        machine

    -- Add final chunk marker if needed
    let machine :=
      if final && machine.sentOutputHead then
        match machine.outputMessage with
        | some msg =>
          if msg.headers.get? "Transfer-Encoding" |>.any (·.contains "chunked") then
            { machine with outputBuffer := machine.outputBuffer ++ formatFinalChunk }
          else machine
        | none => machine
      else machine

    let data := machine.outputBuffer
    let machine := { machine with outputBuffer := .empty }
    (machine, data)
  else
    -- Don't flush yet, just return empty
    (machine, ByteArray.empty)

/--
Advances the state of the machine by feeding it if with a answer.
-/
def answer (machine : Machine mode) (head : Message Data.Body mode.inverse) : Machine mode :=
  match machine.state with
  | .readyToAnswer | .failed _ =>
    let connectionValue := if machine.keepAlive then "keep-alive" else "close"

    let headWithConnection :=
      if head.headers.contains "Connection"
        then head
        else head.addHeader "Connection" connectionValue

    { machine with
      outputMessage := some headWithConnection,
      state := .awaitingAnswer }
  | _ => machine

/--
Handles machine failure by generating error response.
-/
private def handleFailure (machine : Machine mode) (error : Error) : Machine mode :=
  match mode with
  | .request =>
    let errorResponse := error.toResponse
    let errorResponse := { errorResponse with headers := errorResponse.headers.insert "Connection" "close" }
    let machine := answer machine errorResponse

    let machine :=
      match errorResponse.body with
      | .bytes bodyBytes => writeData machine bodyBytes.toByteArray
      | .zero => writeData machine .empty
      | _ => machine

    { machine with state := .closed, event := some .close}

  | .response =>
    { machine with
      state := .closed,
      event := some .close}

/--
Adds to the input buffer.
-/
def feed (machine : Machine mode) (data : ByteArray) : Machine mode :=
  if machine.inputBuffer.array.size == 0 then
    { machine with inputBuffer := data.iter }
  else
    { machine with inputBuffer := {machine.inputBuffer with array := machine.inputBuffer.array ++ data} }

/--
Determines keep-alive status from headers and config
--/
private def determineKeepAlive (machine : Machine mode) : Bool :=
  let connectionHeader := machine.inputHeaders.get? "Connection" |>.getD (HashSet.ofList ["keep-alive"])
  let explicitClose := connectionHeader.contains "close"
  let explicitKeepAlive := connectionHeader.contains "keep-alive"

  if explicitClose then false
  else if explicitKeepAlive then true
  else machine.config.enableKeepAlive && machine.requestCount < machine.config.maxRequests

/--
Updates machine with keep-alive decision
--/
private def updateKeepAlive (machine : Machine mode) : Machine mode :=
  { machine with keepAlive := determineKeepAlive machine }

/--
Common state transition helper.
--/
private def transitionTo (machine : Machine mode) (newState : State) (event : Option (Event mode) := none) : Machine mode :=
  { machine with state := newState, event }

/--
Forces completion of any pending output and transitions to appropriate final state.
Sends final chunk if using chunked encoding.
-/
def close (machine : Machine mode) : Machine mode :=
  if machine.keepAlive
    then machine.transitionTo .next (some .next)
    else machine.transitionTo .closed (some .close)

/--
Single header validation.
--/
private def processHeader (machine : Machine mode) (limit : Nat) (header : Parser.Header) : Machine mode :=
  if limit > machine.config.maxHeaders then
    machine.setError .entityTooLarge
  else
    { machine with
    inputHeaders := machine.inputHeaders.insert header.name header.value,
    state := .needHeader (limit + 1) }

/--
Header validation with keep-alive consideration.
--/
private def processHeaders (machine : Machine mode) : Machine mode :=
  let machine := updateKeepAlive machine
  match validateHeaders mode machine.inputHeaders with
  | none =>
    machine.setError .badRequest
  | some (.fixed n) =>
    machine.transitionTo (.needFixedBody n) (some (.endHeaders (.fixed n)))
  | some .chunked =>
    machine.transitionTo .needChunkedSize (some (.endHeaders .chunked))

/--
Advances the state machine by one step.
-/
def advance (machine : Machine mode) : Machine mode :=
  let machine := { machine with event := none }

  match machine.state with
  | .needStatusLine =>
    let (machine, result) := parseStatusLine machine
    if let some result := result
      then { machine with inputStatusLine := result, state := .needHeader 0 }
      else machine

  | .needHeader limit =>
    let (machine, result) := parseWith machine Parser.parseHeader
    match result with
    | some (some header) =>
      processHeader machine limit header
    | some none =>
      processHeaders machine
    | none =>
      machine

  | .needChunkedSize =>
    let (machine, result) := parseWith machine Parser.parseChunkSize
    match result with
    | some (size, ext) =>
      { machine with size := some size.toUInt64, state := .needChunkedBody size, event := ext <&> Event.chunkExt }
    | none =>
      machine

  | .needChunkedBody 0 =>
    { machine with state := .readyToAnswer, event := some (.gotData true .empty) }

  | .needChunkedBody size =>
    let (machine, result) := parseWith machine (Parser.parseChunkData size)
    match result with
    | some data => { machine with size := none, state := .needChunkedSize, event := some (.gotData false data) }
    | none => machine

  | .needFixedBody size =>
    let (machine, result) := parseWith machine (Parser.parseFixedBody size)
    match result with
    | some data => { machine with size := none, state := .readyToAnswer, event := some (.gotData true data) }
    | none => machine

  | .failed err =>
    handleFailure machine err

  | .readyToAnswer =>
    let buffer : ByteArray := machine.inputBuffer.array.extract machine.inputBuffer.idx machine.inputBuffer.array.size
    { machine with event := some (.readyToRespond), inputBuffer := buffer.iter }

  | .awaitingAnswer =>
    { machine with event := some (.awaitingAnswer) }

  | .awaitingClose =>
    machine

  | .closed =>
    reset machine

  | .next =>
    { machine with state := .closed }

end Machine
