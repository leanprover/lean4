/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Internal.Http.Data
public import Std.Internal.Http.Util
public import Std.Internal.Http.Protocol.H1.Parser

public section

namespace Std
namespace Http
namespace Protocol
namespace H1

open Std Internal Parsec ByteArray
open Util

namespace Machine

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
  Connection timeout in milliseconds.
  -/
  timeoutMilliseconds : Time.Millisecond.Offset := 1000

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  Size threshold for flushing output buffer.
  -/
  highMark : Nat := 4096

  /--
  Default buffer size for the connection
  -/
  defaultPayloadBytes : Nat := 8192

  /--
  The server name
  -/
  serverName : Option String := some "LeanHTTP/1.1"

/--
Specific HTTP processing errors with detailed information.
-/
inductive Error
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

instance : Repr ByteSlice where
  reprPrec x := reprPrec x.toByteArray.data

/--
Events that can occur during HTTP message processing.
-/
inductive Event
  /--
  Event received when chunk extension data is encountered in chunked encoding.
  -/
  | chunkExt (ext : Array (String × Option String))

  /--
  Event received the headers end.
  -/
  | endHeaders (size : Request.Head)

  /--
  Event received when some data arrives from the received thing.
  -/
  | gotData (final : Bool) (data : ByteSlice)

  /--
  Need more data is an event that arrives when the input ended and it requires more
  data to continue
  -/
  | needMoreData (size : Option Nat)

  /--
  Event received when parsing or processing fails with an error message.
  -/
  | failed

  /--
  Event received when connection should be closed.
  -/
  | close

  /--
  Awaiting the next request
  -/
  | next
deriving Inhabited, Repr

inductive Reader.State : Type
  /--
  Initial state waiting for HTTP start line.
  -/
  | needStartLine : State

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
  Requires the response to continue.
  -/
  | requireResponse : Body.Length → State

  /--
  State when request is fully parsed and ready to generate response.
  -/
  | complete : State

  /--
  The input is malformed.
  -/
  | failed (error : Response.Head) : State
deriving Inhabited, Repr

inductive Writer.State
  /--
  Ready to write the response
  -/
  | waitingHeaders

  /--
  This is the state that we wait for a forced flush. This happens and causes the writer to
  start actually writing to the outputData
  -/
  | waitingForFlush

  /--
  Writing the headers.
  -/
  | writingHeaders

  /--
  Writing a fixed size body output.
  -/
  | writingFixedData

  /--
  Writing chunked data.
  -/
  | writingChunkedBody

  /--
  State when response is fully sent and ready to the next request.
  -/
  | complete : State
deriving BEq, Repr

/--
Manages the reading state of the machine.
-/
structure Reader where

  /--
  The current state of the machine.
  -/
  state : Machine.Reader.State := .needStartLine

  /--
  The input byte array.
  -/
  input : ByteArray.Iterator := ByteArray.emptyWithCapacity 4096 |>.iter

  /--
  The request head.
  -/
  request : Request.Head := {}

  /--
  Count of requests that this connection already parsed
  -/
  requestCount : Nat := 0

namespace Reader

@[inline]
def feed (data : ByteArray) (reader : Reader) : Reader :=
  { reader with input :=
    if reader.input.atEnd
      then data.iter
      else { reader.input with array := reader.input.array ++ data } }

@[inline]
def setInput (input : ByteArray.Iterator) (reader : Reader) : Reader :=
  { reader with input }

@[inline]
def setRequest (request : Request.Head) (reader : Reader) : Reader :=
  { reader with request }

@[inline]
def addHeader (name : String) (value : String) (reader : Reader) : Reader :=
  { reader with request := { reader.request with headers := reader.request.headers.insert name value } }

end Reader

/--
Manages the writing state of the machine.
-/
structure Writer where

  /--
  This is all the data that the user is sending that is being accumulated.
  -/
  userData : BufferBuilder := .empty

  /--
  The chunk headers that are going to be with the chunk
  -/
  chunkExt : Array (Array (String × Option String)) := .empty

  /--
  All the data that is going to get out of the writer.
  -/
  outputData : BufferBuilder := .empty

  /--
  This is the size that we need to know or not before sending to the output data. If it's fixed then
  it puts Content-Length instead o Transfer-Encoding chunked
  -/
  isChunked : Bool := false

  /--
  The state of the writer machine. It carries if the reader had already read the headers, the size
  of the output, if it's chunked or not.
  -/
  state : Machine.Writer.State := .waitingHeaders

  /--
  When the user specifies the exact size upfront, we can use Content-Length
  instead of chunked transfer encoding for streaming
  -/
  knownSize : Option Nat := none

  /--
  The Response that will be written to the output
  -/
  response : Response.Head := {}

  /--
  This flags that the writer is closed so if we start to write the body we know exactly the size.
  -/
  closed : Bool := false

namespace Writer

/--
Rests and closes the connection
-/
def resetAndClose (writer : Writer) : Writer :=
  match writer.state with
  | .waitingForFlush =>
    { writer with userData := .empty, closed := true }
  | _ =>
    writer

/--
Close the writer, enabling size determination
--/
@[inline]
def close (writer : Writer) : Writer :=
  { writer with closed := true }

/--
Set a known size for the response body, enabling streaming with Content-Length
-/
@[inline]
def setKnownSize (size : Nat) (writer : Writer) : Writer :=
  { writer with knownSize := some size, isChunked := false }

/--
Determine the body size based on writer state and closure
--/
private def determineBodySize (writer : Writer) : Body.Length :=
  if let some size := writer.knownSize then
    .fixed size
  else if writer.isChunked then
    .chunked
  else if writer.closed then
    .fixed writer.userData.size
  else
    .chunked

/--
Add data to the user data buffer
-/
@[inline]
def addUserData (data : Util.BufferBuilder) (writer : Writer) : Writer :=
  if writer.closed then
    writer
  else
    { writer with userData := writer.userData.append data }

/--
Add data to the user chunk ext buffer
-/
@[inline]
def addChunkExt (data : Array (String × Option String)) (writer : Writer) : Writer :=
  if writer.closed then
    writer
  else
    {  writer with chunkExt := writer.chunkExt.push data }

/--
Write fixed-size body data
-/
private def writeFixedBody (writer : Writer) : Writer :=
  if writer.userData.size = 0 then
    writer
  else
    let data := writer.userData
    { writer with
      userData := BufferBuilder.empty
      outputData := writer.outputData.append data
    }

/--
Write fixed-size body data
-/
private def writeChunkedBody (writer : Writer) : Writer :=
  if writer.userData.size = 0 then
    writer
  else
    let data := writer.userData

    let ext : Array String := writer.chunkExt.take data.size |>.map (Array.foldl
      (fun acc (name, value)  => acc ++ ";" ++ name ++ (value.map (fun x => "=" ++ x) |>.getD ""))
      "")

    let chunks := data.data.mapIdx fun idx ba =>
      let chunkLen := ba.size
      let chunkHeader :=
        (Nat.toDigits 16 chunkLen |>.toArray |>.map Char.toUInt8 |> ByteArray.mk)
        ++ (ext[idx]? |>.map String.toUTF8 |>.getD .empty)
        ++ "\r\n".toUTF8
      chunkHeader ++ ba ++ "\r\n".toUTF8

    { writer with
      userData := BufferBuilder.empty
      chunkExt := writer.chunkExt.drop data.size
      outputData := writer.outputData ++ chunks
    }

private def writeFinalChunk (writer : Writer) : Writer :=
  let writer := writer.writeChunkedBody

  { writer with
    outputData := writer.outputData.append "0\r\n\r\n".toUTF8
    state := .complete
  }

/--
Get the current output data and clear the buffer
-/
@[inline]
def takeOutput (writer : Writer) : Option (Writer × ByteArray) :=
  let output := writer.outputData.toByteArray
  some ({ writer with outputData := BufferBuilder.empty }, output)

/--
Set the writer state
-/
@[inline]
def setState (state : Machine.Writer.State) (writer : Writer) : Writer :=
  { writer with state }

/--
Write response headers to output buffer
-/
private def writeHeaders (response : Response.Head) (writer : Writer) : Writer :=
  { writer with outputData := writer.outputData.push (toString response).toUTF8 }

end Writer
end Machine

/--
The state machine that receives some input bytes and outputs bytes for the HTTP 1.1 protocol.
-/
structure Machine where

  /--
  The state of the reader.
  -/
  reader : Machine.Reader := {}

  /--
  The state of the writer.
  -/
  writer : Machine.Writer := {}

  /--
  The configuration of the machine.
  -/
  config : Machine.Config := {}

  /--
  Events that happend during reading and writing.
  -/
  events : Array Machine.Event := #[]

  /--
  Error thrown by the machine
  -/
  error : Option Machine.Error := none

  /--
  The timestamp that will be used to create the `Date` header.
  -/
  instant : Option (Std.Time.DateTime .UTC) := none

  /--
  If the request will be kept alive after the request.
  -/
  keepAlive : Bool := false

namespace Machine

private def shouldBreakConnection (c : Status) : Bool :=
  match c with
  | .uriTooLong
  | .badRequest
  | .payloadTooLarge
  | .requestHeaderFieldsTooLarge => true
  | _ => false

-- Additional helper functions for writer manipulation
@[inline]
private def modifyWriter (machine : Machine) (fn : Writer → Writer) : Machine :=
  { machine with writer := fn machine.writer }

@[inline]
private def resetAndClose (machine : Machine) : Machine :=
  machine.modifyWriter (·.resetAndClose)

@[inline]
private def setWriterState (machine : Machine) (state : Writer.State) : Machine :=
  machine.modifyWriter ({ · with state })

@[inline]
private def addEvent (machine : Machine) (event : Event) : Machine :=
  { machine with events := machine.events.push event }

@[inline]
private def setEvent (machine : Machine) (event : Option Event) : Machine :=
  match event with
  | some event => machine.addEvent event
  | none => machine

@[inline]
private def setError (machine : Machine) (error : Machine.Error) : Machine :=
  { machine with error := some error }

@[inline]
private def closeConnection (machine : Machine) : Machine :=
  { machine with keepAlive := false }

@[inline]
private def modifyReader (machine : Machine) (fn : Reader → Reader) : Machine :=
  { machine with reader := fn machine.reader }

@[inline]
private def setReaderState (machine : Machine) (state : Reader.State) : Machine :=
  machine.modifyReader ({ · with state })

@[inline]
def setFailure (machine : Machine) (error : H1.Machine.Error) (status : Status) : Machine :=
  machine
  |>.addEvent .failed
  |>.setReaderState (.failed { status })
  |>.setError error

private def parseWith (machine : Machine) (parser : Parser α) (limit : Option Nat) (expect : Option Nat := none) : (Machine × Option α) :=
  let remaining := machine.reader.input.remainingBytes
    match parser machine.reader.input with
  | .success buffer reqLine => ({ machine with reader := machine.reader.setInput buffer }, some reqLine)
  | .error it .eof =>
    let usedBytesUntilFailure := remaining - it.remainingBytes

    if let some limit := limit then
      if usedBytesUntilFailure ≥ limit
        then (machine.setFailure .badRequest .badRequest, none)
        else (machine.addEvent (.needMoreData expect), none)
    else (machine.addEvent (.needMoreData expect), none)
  | .error _ _ =>
    (machine.setFailure .badRequest .badRequest, none)

/--
Set a known size for the response body
-/
@[inline]
def setKnownSize (machine : Machine) (size : Nat) : Machine :=
  { machine with writer := machine.writer.setKnownSize size }

/--
Reset the machine for the next request after response is complete
-/
private def resetForNextRequest (machine : Machine) : Machine :=
  let newRequestCount := machine.reader.requestCount + 1
  let shouldKeepAlive := machine.keepAlive && newRequestCount < machine.config.maxRequests

  if shouldKeepAlive then
    { machine with
      reader := {
        state := .needStartLine,
        input := machine.reader.input,
        request := {},
        requestCount := newRequestCount
      },
      writer := {
        userData := .empty,
        chunkExt := .empty,
        outputData := machine.writer.outputData,
        isChunked := false,
        state := .waitingHeaders,
        closed := false,
        knownSize := none,
        response := {},
      },
      events := machine.events.push .next,
      error := none,
      instant := none
    }
  else
    machine.addEvent .close

-- Validation of request

private def determineKeepAlive (machine : Machine) : Bool :=
  let connectionHeader := machine.reader.request.headers.get? "Connection" |>.getD (HashSet.ofList ["keep-alive"])
  let explicitClose := connectionHeader.contains "close"
  let explicitKeepAlive := connectionHeader.contains "keep-alive"

  if explicitClose then false
  else if explicitKeepAlive then true
  else machine.config.enableKeepAlive && machine.reader.requestCount < machine.config.maxRequests

@[inline]
private def updateKeepAlive (machine : Machine) : Machine :=
  { machine with keepAlive := determineKeepAlive machine }

-- https://datatracker.ietf.org/doc/html/rfc7230#section-3.3.3
def getRequestSize (req : Request.Head) : Option Body.Length := do
  guard (req.headers.get? "host" |>.isSome)

  if req.method == .head ∨ req.method == .connect then
    return .fixed 0

  match (req.headers.getSingle? "Content-Length", req.headers.get? "Transfer-Encoding") with
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
  | (some _, some _) =>
    some .chunked

private def processHeaders (machine : Machine) : Machine :=
  let machine := updateKeepAlive machine

  match getRequestSize machine.reader.request with
  | none =>
    machine.setFailure .badRequest .badRequest
  | some size =>
    machine
    |>.addEvent (.endHeaders machine.reader.request)
    |>.setReaderState <| match size with
      | .fixed n => .needFixedBody n
      | .chunked => .needChunkedSize

/--
Set response headers and determine transfer mode
-/
def setHeaders (response : Response.Head) (machine : Machine) : Machine :=
  let size := Writer.determineBodySize machine.writer

  let headers :=
    if let some server := machine.config.serverName then
      response.headers
      |>.insert "Server" server
    else
      response.headers

  let headers := if let some date := machine.instant then headers.insert "Date" (date.format "EEE, dd MMM yyyy HH:mm:ss 'GMT'")  else  headers

  let headers := if ¬machine.keepAlive ∨ shouldBreakConnection response.status then
    headers.insert "Connection" "close"
  else
    headers

  let response := { response with headers }

  let response := match size with
    | .fixed 0 => response
    | .fixed n => { response with headers := response.headers.insert "Content-Length" (toString n) }
    | .chunked => { response with headers := response.headers.insert "Transfer-Encoding" "chunked" }

  let state := match size with
    | .fixed _ => Machine.Writer.State.writingFixedData
    | .chunked => Machine.Writer.State.writingChunkedBody

  machine.modifyWriter (fun writer => {
    writer with
    outputData := writer.outputData.append (toString response).toUTF8,
    state })

/--
Remove all the events in the machine
-/
@[inline]
def takeEvents (machine : Machine) : Machine × Array Event :=
  if machine.events.isEmpty then
    (machine, machine.events)
  else
    ({ machine with events := #[] }, machine.events)

/--
Put some data inside the input of the machine.
-/
@[inline]
def feed (machine : Machine) (data : ByteArray) : Machine :=
  { machine with reader := machine.reader.feed data }

/--
Put some data inside the input of the machine.
-/
@[inline]
def setNow (machine : Machine) : IO Machine := do
  return { machine with instant := some (← Std.Time.DateTime.now) }

/--
Put some data inside the input of the machine.
-/
@[inline]
def writeUserData (machine : Machine) (data : Util.BufferBuilder) : Machine :=
  { machine with writer := machine.writer.addUserData data }

/--
Put some data inside the input of the machine.
-/
@[inline]
def writeChunkExt (machine : Machine) (chunkExt : Array (String × Option String)) : Machine :=
  { machine with writer := machine.writer.addChunkExt chunkExt }

/--
Put some data inside the input of the machine.
-/
@[inline]
def closeWriter (machine : Machine) : Machine :=
  { machine with writer := machine.writer.close }

def isWriterOpened (machine : Machine) : Bool :=
  ¬machine.writer.closed

def isWaitingResponse (machine : Machine) : Bool :=
  match machine.writer.state with
  | .waitingHeaders => true
  | _ => false

/--
Sends the response
-/
def sendResponse (machine : Machine) (response : Response.Head) : Machine :=
  match machine.writer.state with
  | .waitingHeaders =>
    let machine := machine.modifyWriter ({ · with response, state := .waitingForFlush })
    let conn := response.headers.getD "Connection"

    if conn.contains "close" then
      machine
      |>.closeConnection
      |>.setReaderState .complete
    else
      machine

  | _ =>
    machine

def isReaderComplete (machine : Machine) : Bool :=
  match machine.reader.state with
  | .complete => true
  | _ => false

/--
Advances the state of the reader.
-/
partial def processRead (machine : Machine) : Machine :=
  match machine.reader.state with
  | .needStartLine =>
    let (machine, result) := parseWith machine parseRequestLine (limit := some 8192)

    if let some head := result then
      machine
      |>.modifyReader (.setRequest head)
      |>.setReaderState (.needHeader 0)
      |>.processRead
    else
      machine

  | .needHeader headerCount =>
    let (machine, result) := parseWith machine (parseSingleHeader machine.config.maxHeaderSize) (limit := none)

    if headerCount > machine.config.maxHeaders then
      machine |>.setFailure .badRequest .badRequest
    else
      if let some result := result then
        if let some (name, value) := result then
          machine
          |>.modifyReader (.addHeader name value)
          |>.setReaderState (.needHeader (headerCount + 1))
          |>.processRead
        else
          processHeaders machine
      else
        machine

  | .requireResponse _ =>
    machine

  | .needChunkedSize =>
    let (machine, result) := parseWith machine parseChunkSize (limit := some 128)

    match result with
    | some (size, ext) =>
      machine
      |>.setReaderState (.needChunkedBody size)
      |>.setEvent (some ext <&> .chunkExt)
      |>.processRead
    | none =>
      machine

  | .needChunkedBody size =>
    let (machine, result) := parseWith machine (parseChunkedSizedData size) (limit := none) (some size)

    if let some body := result then
      match body with
      | .complete body =>
        if size ≠ 0 then
          machine
          |>.setReaderState .needChunkedSize
          |>.addEvent (.gotData false body)
          |>.processRead
        else
          machine
          |>.setReaderState .complete
          |>.addEvent (.gotData true .empty)
          |>.processRead
      | .incomplete body remaining => machine
        |>.setReaderState (.needChunkedBody remaining)
        |>.addEvent (.gotData false body)
    else
      machine

  | .needFixedBody 0 =>
    machine
    |>.setReaderState .complete
    |>.addEvent (.gotData true .empty)
    |>.processRead

  | .needFixedBody size =>
    let (machine, result) := parseWith machine (parseFixedSizeData size) (limit := none) (some size)

    if let some body := result then
      match body with
      | .complete body =>
        machine
        |>.setReaderState .complete
        |>.addEvent (.gotData true body)
        |>.processRead
      | .incomplete body remaining =>
        machine
        |>.setReaderState (.needFixedBody remaining)
        |>.addEvent (.gotData false body)
    else
      machine

  | .complete =>
    machine

  | .failed response =>
    machine
    |>.sendResponse response
    |>.resetAndClose
    |>.setReaderState .complete
    |>.closeConnection

def failed (machine : Machine) : Bool :=
  match machine.reader.state with
  | .failed _ => true
  | _ => false

def shouldFlush (machine : Machine) : Bool :=
  machine.failed ∨
  machine.writer.userData.size ≥ machine.config.highMark ∨
  machine.writer.closed

/--
Get the current output data and clear the buffer
-/
@[inline]
def takeOutput (machine : Machine) (highMark := 0): Option (Machine × BufferBuilder) :=
  if machine.writer.outputData.size ≥ highMark ∨
    machine.writer.state == .complete
  then
    let output := machine.writer.outputData
    some ({ machine with writer := { machine.writer with outputData := .empty } }, output)
  else
    none

/--
Write response data to the machine
-/
partial def processWrite (machine : Machine) : Machine :=
  match machine.writer.state with
  | .waitingHeaders =>
    machine

  | .waitingForFlush =>
    if machine.shouldFlush then
      machine.setHeaders machine.writer.response |>.processWrite
    else
      machine

  | .writingFixedData =>
    if machine.writer.userData.size ≥ machine.config.highMark ∨ machine.writer.closed then
      let machine := machine.modifyWriter Writer.writeFixedBody
      if machine.writer.closed then
        machine.setWriterState .complete |>.processWrite
      else
        machine
    else
      machine

  | .writingChunkedBody =>
    if machine.writer.closed then
      machine.modifyWriter Writer.writeFinalChunk |>.processWrite
    else if machine.writer.userData.size ≥ machine.config.highMark then
      machine.modifyWriter Writer.writeChunkedBody |>.processWrite
    else
      machine

  | .complete =>
    resetForNextRequest machine

  | .writingHeaders =>
    machine

end Machine
