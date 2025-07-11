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

open Std.Internal.Parsec.ByteArray (Parser)

namespace Std
namespace Http
namespace V11

set_option linter.all true

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

/--
Determines the type of the status line based on the Mode.
-/
abbrev StatusLine : Mode → Type
  | .request => Data.Method × String × Data.Version
  | .response => Data.Version × Data.Status × String

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

/--
Gets the headers
-/
def headers (message : Message t mode) : Data.Headers :=
  match mode with
  | .request => Data.Request.headers message
  | .response => Data.Response.headers message

/--
Insert headers
-/
def addHeader (message : Message t mode) (k : String) (v : String) : Message t mode :=
  match mode with
  | .request => { message with headers := message.headers.insert k v }
  | .response => { message with headers := message.headers.insert k v }

/--
Inverts the mode.
-/
def Mode.inverse : Mode → Mode
  | .request => .response
  | .response => .request

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
Errors that can occur and should trigger a response.
-/
inductive Error where
  /--
  Client sent malformed or invalid request
  -/
  | badRequest

  /--
  Other error with custom message
  -/
  | other (s : String)
deriving Repr, BEq

/--
Events that can occur during HTTP message processing.
-/
inductive Event (mode : Mode)
  /--
  Event received when chunk extension data is encountered in chunked encoding.
  -/
  | chunkExt (ext : ByteArray)

  /--
  Event received the headers end.
  -/
  | endHeaders (size : Size)

  /--
  Event received when some data arrives from the received thing.
  -/
  | gotData (final : Bool) (data : ByteArray)

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
  Final state when connection is closed.
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
  inputBuffer : ByteArray.Iterator := ByteArray.empty.iter

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
  event : Option (Event mode) := none

  /--
  The highmark used for flushign the bytearray
  -/
  highMark : Nat := 4096

  /--
  Check if the answer is chunked
  -/
  chunkedAnswer : Bool := false
  /--
  Whether connection should be kept alive after current transaction
  -/
  keepAlive : Bool := true

  /--
  Maximum number of requests allowed on this connection
  -/
  maxRequests : Nat := 100

  /--
  Current request count on this connection
  -/
  requestCount : Nat := 0

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

private def setBadRequest (machine : Machine mode) : Machine mode :=
  { machine with state := .failed .badRequest, event := some (.failed .badRequest) }

private def parseWith (machine : Machine mode) (parser : Parser α) : (Machine mode × Option α) :=
  match parser machine.inputBuffer with
  | .success buffer reqLine => ({ machine with inputBuffer := buffer }, some reqLine)
  | .error _ .eof =>  ({ machine with event := some .needMoreData }, none)
  | .error _ _ => (setBadRequest machine, none)

private def parseStatus (machine : Machine mode) : (Machine mode × Option (StatusLine mode)) :=
  match mode with
  | .request =>
    let (machine, result) := parseWith machine Parser.parseRequestLine

    if let some result := result then
      let result : Option (StatusLine .request) := do
        let version ← Data.Version.fromNumber? (result.major.toNat - 48) (result.minor.toNat - 48)
        let method ← Data.Method.fromString? =<< String.fromUTF8? result.method
        let uri ← String.fromUTF8? result.uri
        pure (method, uri, version)

      (machine, result)
    else
      (machine, none)
  | .response =>
    let (machine, result) := parseWith machine Parser.parseStatusLine

    if let some result := result then
      let result : Option (StatusLine .response) := do
        let version ← Data.Version.fromNumber? (result.major.toNat - 48) (result.minor.toNat - 48)
        let status ← Data.Status.fromCode? result.statusCode
        let reason ← String.fromUTF8? result.reasonPhrase
        some (version, status, reason)
      (machine, result)
    else
      (machine, none)

/--
Formats a chunk for chunked transfer encoding.
-/
private def formatChunk (data : ByteArray) : ByteArray :=
  let sizeHex := Nat.toDigits 16 data.size
    |>.map (fun d => if d.toUInt8 < 10 then 48 + d.toUInt8 else 55 + d.toUInt8)
    |>.toByteArray

  sizeHex ++ "\r\n".toUTF8 ++ data ++ "\r\n".toUTF8

/--
Formats the final chunk for chunked transfer encoding.
-/
private def formatFinalChunk : ByteArray :=
  "0\r\n\r\n".toUTF8

private def validateHeaders (headers : Data.Headers) : Option Size := do
  let _host ← headers.get? "host"
  -- todo: check host
  match (headers.get? "Content-Length", headers.get? "Transfer-Encoding") with
  | (some cl, none) => do
    let num ← cl.toNat?
    some (.fixed num)
  | (none, some "chunked") =>
    some .chunked
  | (none, none) =>
    some (.fixed 0)
  | _ => none

/--
Flushes the output buffer and returns the data to send.
-/
def flush (machine : Machine mode) : Machine mode × ByteArray :=
  let data := machine.outputBuffer
  let machine' := { machine with outputBuffer := .empty }
  (machine', data)

/--
Checks if output buffer exceeds high water mark and needs flushing.
-/
def needsFlush (machine : Machine mode) : Bool :=
  machine.outputBuffer.size >= machine.highMark ||
    match machine.state with
    | .closed => true
    | .failed _ => true
    | _ => false

/--
Adds to the input buffer.
-/
def incomeFeed (machine : Machine mode) (data : ByteArray) : Machine mode :=
  { machine with inputBuffer := {machine.inputBuffer with array := machine.inputBuffer.array ++ data} }

/--

-/
def resetEvent (machine : Machine mode) : Machine mode :=
  { machine with event := none }

/--
Resets the machine for a new request on the same connection (keep-alive)
-/
def reset (machine : Machine mode) : Machine mode :=
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
    event := none,
    chunkedAnswer := false,
    requestCount := machine.requestCount + 1 }

/--
Advances the state of the machine by feeding it if with a answer.
-/
def answer (machine : Machine mode) (head : Message Data.Body mode.inverse) : Machine mode :=
  match machine.state with
  | .readyToAnswer =>
    { machine with
      outputMessage := some head,
      state := .awaitingAnswer }
  | .failed _ =>
    { machine with
      outputMessage := some head }
  | _ => machine

/--
Writes data to the output buffer, ensuring the message head is sent first based on the given Size.
-/
def writeToOutputBuffer (machine : Machine mode) (data : ByteArray) (size : Size) : Machine mode :=
  let machine :=
    if not machine.sentOutputHead then
      match machine.outputMessage with
      | some msg =>
        let msgWithHeader :=
          match size with
          | .chunked => addHeader msg "Transfer-Encoding" "chunked"
          | .fixed 0 => msg
          | .fixed n => addHeader msg "Content-Length" (toString n)

        let headBytes := (toString msgWithHeader).toUTF8

        { machine with
          outputMessage := some msgWithHeader,
          outputBuffer := machine.outputBuffer ++ headBytes,
          sentOutputHead := true }
      | none => machine
    else
      machine

  match size with
  | .chunked =>
    let chunk := formatChunk data
    { machine with outputBuffer := machine.outputBuffer.append chunk }
  | .fixed _ =>
    { machine with outputBuffer := machine.outputBuffer.append data }

/--
Adds data to the output buffer, handling chunked/fixed encoding.
Uses exact highMark for chunked encoding unless force is set.
-/
def writeData (machine : Machine mode) (data : ByteArray) (force : Bool := false) : Machine mode :=
  if machine.chunkedAnswer then
    let machine := { machine with chunkedData := machine.chunkedData ++ data }

    if force || machine.chunkedData.size >= machine.highMark then
      if machine.chunkedData.size > 0 then
        let machine := writeToOutputBuffer machine machine.chunkedData .chunked
        { machine with chunkedData := .empty }
      else
        machine
    else
      machine
  else
    let machine := { machine with chunkedData := machine.chunkedData ++ data }

    if force then
      let totalSize := machine.chunkedData.size
      let machine := writeToOutputBuffer machine machine.chunkedData (.fixed totalSize)
      { machine with chunkedData := .empty }
    else
      machine

/--
Determines if connection should be kept alive based on headers and machine state
-/
def shouldKeepAlive (machine : Machine mode) : Bool :=
  let connectionHeader := machine.inputHeaders.get? "Connection" |>.getD ""
  let explicitClose := connectionHeader.toLower == "close"
  let explicitKeepAlive := connectionHeader.toLower == "keep-alive"

  if explicitClose then false
  else if explicitKeepAlive then true
  else machine.keepAlive && machine.requestCount < machine.maxRequests

/--
Forces completion of any pending output and transitions to appropriate final state.
Sends final chunk if using chunked encoding.
-/
def close (machine : Machine mode) : Machine mode :=
  let machine :=
    if machine.chunkedAnswer then
      let machine := writeData machine .empty true
      { machine with outputBuffer := machine.outputBuffer ++ formatFinalChunk }
    else
      writeData machine .empty true

  { machine with
    state := .closed,
    event := some (if shouldKeepAlive machine then .next else .close) }

/--
Creates an appropriate error response based on the error type
-/
private def createErrorResponse (error : Error) : Data.Response Data.Body :=
  match error with
  | .badRequest => {
      status := .badRequest,
      version := .v11,
      headers := .empty
      body := .zero
    }
  | .other _ => {
      status := .internalServerError,
      version := .v11,
      headers := .empty
      body := .zero
    }

/--
Handles failed state by creating error response and transitioning to closed state
-/
private def handleFailure (machine : Machine mode) (error : Error) : Machine mode :=
  match mode with
  | .request =>
    let errorResponse := createErrorResponse error
    let errorResponse := { errorResponse with headers := errorResponse.headers.insert "Connection" "close" }
    let machine := answer machine errorResponse

    let machine :=
      match errorResponse.body with
      | .bytes bodyBytes => writeData machine bodyBytes true
      | .zero => writeData machine .empty true
      | _ => machine

    { machine with state := .closed, event := some .close}

  | .response =>
    { machine with
      state := .closed,
      event := some .close}

/--
Advances the state of the machine and create events.
-/
def advance (machine : Machine mode) : Machine mode :=
  match machine.state with
  | .needStatusLine =>
    let (machine, result) := parseStatus machine

    if let some result := result then
      -- todo: check version.
      { machine with inputStatusLine := result, state := .needHeader 0 }
    else
      machine
  | .needHeader limit =>
    let (machine, result) := parseWith machine Parser.parseHeader
    match result with
    | some (some header) =>
      { machine with
        inputHeaders := machine.inputHeaders.insert header.name header.value,
        state := .needHeader (limit + 1) }
    | some none =>
      match validateHeaders machine.inputHeaders with
      | none => setBadRequest machine
      | some (.fixed n) => { machine with state := .needFixedBody n, event := some (.endHeaders (.fixed n)) }
      | some .chunked => { machine with state := .needChunkedSize, event := some (.endHeaders .chunked) }
    | none => machine
  | .needChunkedSize =>
    let (machine, result) := parseWith machine Parser.parseChunkSize
    match result with
    | some (size, ext) => { machine with state := .needChunkedBody size, event := ext <&> Event.chunkExt }
    | none => machine
  | .needChunkedBody 0 =>
    { machine with state := .readyToAnswer, event := some (.gotData true .empty) }
  | .needChunkedBody size =>
    let (machine, result) := parseWith machine (Parser.parseChunkData size)
    match result with
    | some data => { machine with state := .needChunkedSize, event := some (.gotData false data) }
    | none => machine
  | .needFixedBody size =>
    let (machine, result) := parseWith machine (Parser.parseFixedBody size)
    match result with
    | some data => { machine with state := .readyToAnswer, event := some (.gotData true data) }
    | none => machine
  | .failed err => handleFailure machine err
  | .readyToAnswer => { machine with event := some (.readyToRespond)  }
  | .awaitingAnswer => { machine with event := some (.awaitingAnswer) }
  | .awaitingClose => machine
  | .closed => reset machine

end Machine
