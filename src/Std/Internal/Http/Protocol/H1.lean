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

public section

namespace Std.Http.Protocol.H1

open Std Internal Parsec ByteArray
open Internal

namespace Machine

inductive MachineType
  | request
  | response

/--
Get the message head type based on machine type
-/
@[expose]
def MessageHead : MachineType → Type
  | .request => Request.Head
  | .response => Response.Head

instance : Repr (MessageHead ty) :=
    match ty with
    | .request => inferInstanceAs (Repr Request.Head)
    | .response => inferInstanceAs (Repr Response.Head)

instance : ToString (MessageHead ty) :=
    match ty with
    | .request => inferInstanceAs (ToString Request.Head)
    | .response => inferInstanceAs (ToString Response.Head)

/--
Get the error message head type (opposite of MessageHead)
-/
abbrev ErrorHead : MachineType → Type
  | .request => Response.Head
  | .response => Request.Head

/--
Swap machine type
-/
abbrev MachineType.swap : MachineType → MachineType
  | .request => .response
  | .response => .request

/--
Swap machine type
-/
def MessageHead.headers (m : MessageHead ty) : Headers :=
  match ty with
  | .request => Request.Head.headers m
  | .response => Response.Head.headers m

/--
Connection limits configuration with validation.
-/
structure Config where
  /--
  Maximum number of messages per connection.
  -/
  maxMessages : Nat := 100

  /--
  Maximum number of headers allowed per message.
  -/
  maxHeaders : Nat := 50

  /--
  Maximum size of a single header value.
  -/
  maxHeaderSize : Nat := 8192

  /--
  Whether to enable keep-alive connections by default.
  -/
  enableKeepAlive : Bool := true

  /--
  Size threshold for flushing output buffer.
  -/
  highMark : Nat := 4096

  /--
  The server name (for response mode) or user agent (for request mode)
  -/
  identityHeader : Option HeaderValue := some (.new "LeanHTTP/1.1")

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
  Bad request/response
  -/
  | badMessage

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
inductive Event (ty : MachineType)
  /--
  Event received when chunk extension data is encountered in chunked encoding.
  -/
  | chunkExt (ext : Array (String × Option String))

  /--
  Event received when the headers end.
  -/
  | endHeaders (head : MessageHead ty)

  /--
  Event received when some data arrives from the received message.
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
  Awaiting the next message
  -/
  | next
deriving Inhabited, Repr

inductive Reader.State (ty : MachineType) : Type
  /--
  Initial state waiting for HTTP start line.
  -/
  | needStartLine : State ty

  /--
  State waiting for HTTP headers, tracking number of headers parsed.
  -/
  | needHeader : Nat → State ty

  /--
  State waiting for chunk size in chunked transfer encoding.
  -/
  | needChunkedSize : State ty

  /--
  State waiting for chunk body data of specified size.
  -/
  | needChunkedBody : Nat → State ty

  /--
  State waiting for fixed-length body data of specified size.
  -/
  | needFixedBody : Nat → State ty

  /--
  Requires the outgoing message to continue.
  -/
  | requireOutgoing : Body.Length → State ty

  /--
  State when message is fully parsed and ready.
  -/
  | complete : State ty

  /--
  The input is malformed.
  -/
  | failed (error : Error) : State ty
deriving Inhabited, Repr

inductive Writer.State
  /--
  Ready to write the message
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
  State when message is fully sent and ready for the next message.
  -/
  | complete : State
deriving BEq, Repr

structure Reader (ty : MachineType) where
  /--
  The current state of the machine.
  -/
  state : Machine.Reader.State ty := .needStartLine

  /--
  The input byte array.
  -/
  input : ByteArray.Iterator := ByteArray.emptyWithCapacity 4096 |>.iter

  /--
  The incoming message head.
  -/
  messageHead : MessageHead ty := match ty with
    | .request => {}
    | .response => {}

  /--
  Count of messages that this connection already parsed
  -/
  messageCount : Nat := 0

namespace Reader

@[inline]
def feed (data : ByteArray) (reader : Reader ty) : Reader ty :=
  { reader with input :=
    if reader.input.atEnd
      then data.iter
      else { reader.input with array := reader.input.array ++ data } }

@[inline]
def setInput (input : ByteArray.Iterator) (reader : Reader ty) : Reader ty :=
  { reader with input }

@[inline]
def setMessageHead (messageHead : MessageHead ty) (reader : Reader ty) : Reader ty :=
  { reader with messageHead }

@[inline]
def addHeader (name : String) (value : HeaderValue) (reader : Reader ty) : Reader ty :=
  match ty with
  | .request =>
    { reader with messageHead := { reader.messageHead with headers := reader.messageHead.headers.insert name value } }
  | .response =>
    { reader with messageHead := { reader.messageHead with headers := reader.messageHead.headers.insert name value } }

end Reader

/--
Manages the writing state of the machine.
-/
structure Writer (ty : MachineType) where
  /--
  This is all the data that the user is sending that is being accumulated.
  -/
  userData : ChunkedBuffer := .empty

  /--
  The chunk headers that are going to be with the chunk
  -/
  chunkExt : Array (Array (String × Option String)) := .empty

  /--
  All the data that is going to get out of the writer.
  -/
  outputData : ChunkedBuffer := .empty

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
  The outgoing message that will be written to the output
  -/
  messageHead : MessageHead ty.swap := match ty with
    | .request => {}
    | .response => {}

  /--
  This flags that the writer is closed so if we start to write the body we know exactly the size.
  -/
  closed : Bool := false

namespace Writer

/--
Resets and closes the connection
-/
def resetAndClose (writer : Writer ty) : Writer ty :=
  match writer.state with
  | .waitingForFlush =>
    { writer with userData := .empty, closed := true }
  | _ =>
    writer

/--
Close the writer, enabling size determination
--/
@[inline]
def close (writer : Writer ty) : Writer ty :=
  { writer with closed := true }

/--
Set a known size for the message body, enabling streaming with Content-Length
-/
@[inline]
def setKnownSize (size : Nat) (writer : Writer ty) : Writer ty :=
  { writer with knownSize := some size }

/--
Determine the body size based on writer state and closure
--/
private def determineBodySize (writer : Writer ty) : Body.Length :=
  if let some size := writer.knownSize then
    .fixed size
  else if writer.closed then
    .fixed writer.userData.size
  else
    .chunked

/--
Add data to the user data buffer
-/
@[inline]
def addUserData (data : ChunkedBuffer) (writer : Writer ty) : Writer ty :=
  if writer.closed then
    writer
  else
    { writer with userData := writer.userData.append data }

/--
Add data to the user chunk ext buffer
-/
@[inline]
def addChunkExt (data : Array (String × Option String)) (writer : Writer ty) : Writer ty :=
  if writer.closed then
    writer
  else
    {  writer with chunkExt := writer.chunkExt.push data }

/--
Write fixed-size body data
-/
private def writeFixedBody (writer : Writer ty) : Writer ty :=
  if writer.userData.size = 0 then
    writer
  else
    let data := writer.userData
    { writer with
      userData := ChunkedBuffer.empty
      outputData := writer.outputData.append data
    }

/--
Write chunked body data
-/
private def writeChunkedBody (writer : Writer ty) : Writer ty :=
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
      userData := ChunkedBuffer.empty
      chunkExt := writer.chunkExt.drop data.size
      outputData := writer.outputData ++ chunks
    }

private def writeFinalChunk (writer : Writer ty) : Writer ty :=
  let writer := writer.writeChunkedBody

  { writer with
    outputData := writer.outputData.append "0\r\n\r\n".toUTF8
    state := .complete
  }

/--
Get the current output data and clear the buffer
-/
@[inline]
def takeOutput (writer : Writer ty) : Option (Writer ty × ByteArray) :=
  let output := writer.outputData.toByteArray
  some ({ writer with outputData := ChunkedBuffer.empty }, output)

/--
Set the writer state
-/
@[inline]
def setState (state : Machine.Writer.State) (writer : Writer ty) : Writer ty :=
  { writer with state }

/--
Write message headers to output buffer
-/
private def writeHeaders (messageHead : MessageHead ty) (writer : Writer ty) : Writer ty :=
  { writer with outputData := writer.outputData.push (toString messageHead).toUTF8 }

end Writer
end Machine

/--
The state machine that receives some input bytes and outputs bytes for the HTTP 1.1 protocol.
-/
structure Machine (ty : Machine.MachineType) where
  /--
  The state of the reader.
  -/
  reader : Machine.Reader ty := {}

  /--
  The state of the writer.
  -/
  writer : Machine.Writer ty := {}

  /--
  The configuration of the machine.
  -/
  config : Machine.Config := {}

  /--
  Events that happened during reading and writing.
  -/
  events : Array (Machine.Event ty) := #[]

  /--
  Error thrown by the machine
  -/
  error : Option Machine.Error := none

  /--
  The timestamp that will be used to create the `Date` header.
  -/
  instant : Option (Std.Time.DateTime .UTC) := none

  /--
  If the connection will be kept alive after the message.
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
private def modifyWriter (machine : Machine ty) (fn : Writer ty → Writer ty) : Machine ty :=
  { machine with writer := fn machine.writer }

@[inline]
private def resetAndClose (machine : Machine ty) : Machine ty :=
  machine.modifyWriter (·.resetAndClose)

@[inline]
private def setWriterState (machine : Machine ty) (state : Writer.State) : Machine ty :=
  machine.modifyWriter ({ · with state })

@[inline]
private def addEvent (machine : Machine ty) (event : Event ty) : Machine ty :=
  { machine with events := machine.events.push event }

@[inline]
private def setEvent (machine : Machine ty) (event : Option (Event ty)) : Machine ty :=
  match event with
  | some event => machine.addEvent event
  | none => machine

@[inline]
private def setError (machine : Machine ty) (error : Machine.Error) : Machine ty :=
  { machine with error := some error }

@[inline]
private def closeConnection (machine : Machine ty) : Machine ty :=
  { machine with keepAlive := false }

@[inline]
private def modifyReader (machine : Machine ty) (fn : Reader ty → Reader ty) : Machine ty :=
  { machine with reader := fn machine.reader }

@[inline]
private def setReaderState (machine : Machine ty) (state : Reader.State ty) : Machine ty :=
  machine.modifyReader ({ · with state })

@[inline]
def setFailure (machine : Machine ty) (error : H1.Machine.Error) : Machine ty :=
  machine
  |>.addEvent .failed
  |>.setReaderState (.failed error)
  |>.setError error

private def parseWith (machine : Machine ty) (parser : Parser α) (limit : Option Nat) (expect : Option Nat := none) : (Machine ty × Option α) :=
  let remaining := machine.reader.input.remainingBytes
    match parser machine.reader.input with
  | .success buffer result => ({ machine with reader := machine.reader.setInput buffer }, some result)
  | .error it .eof =>
    let usedBytesUntilFailure := remaining - it.remainingBytes

    if let some limit := limit then
      if usedBytesUntilFailure ≥ limit
        then (machine.setFailure .badMessage, none)
        else (machine.addEvent (.needMoreData expect), none)
    else (machine.addEvent (.needMoreData expect), none)
  | .error _ _ =>
    (machine.setFailure .badMessage, none)

/--
Set a known size for the message body
-/
@[inline]
def setKnownSize (machine : Machine ty) (size : Nat) : Machine ty :=
  { machine with writer := machine.writer.setKnownSize size }

/--
Reset the machine for the next message after current message is complete
-/
private def resetForNextMessage (machine : Machine ty) : Machine ty :=
  let newMessageCount := machine.reader.messageCount + 1
  let shouldKeepAlive := machine.keepAlive && newMessageCount < machine.config.maxMessages

  if shouldKeepAlive then
    { machine with
      reader := {
        state := .needStartLine,
        input := machine.reader.input,
        messageHead := match ty with | .request => {} | .response => {},
        messageCount := newMessageCount
      },
      writer := {
        userData := .empty,
        chunkExt := .empty,
        outputData := machine.writer.outputData,
        state := .waitingHeaders,
        closed := false,
        knownSize := none,
        messageHead := match ty with | .request => {} | .response => {},
      },
      events := machine.events.push .next,
      error := none,
      instant := none
    }
  else
    machine.addEvent .close

-- Validation of message

private def determineKeepAlive (machine : Machine ty) : Bool :=
  let headers := match ty with
    | .request => machine.reader.messageHead.headers
    | .response => machine.reader.messageHead.headers
  let connectionHeader := headers.getLast? "Connection" |>.getD (.new "keep-alive")
  let explicitClose := connectionHeader.is "close"
  let explicitKeepAlive := connectionHeader.is "keep-alive"

  if explicitClose then false
  else if explicitKeepAlive then true
  else machine.config.enableKeepAlive && machine.reader.messageCount < machine.config.maxMessages

@[inline]
private def updateKeepAlive (machine : Machine ty) : Machine ty :=
  { machine with keepAlive := determineKeepAlive machine }

-- https://datatracker.ietf.org/doc/html/rfc7230#section-3.3.3
def getMessageSize (req : MessageHead ty) : Option Body.Length := do
  match ty with
  | .request => guard (req.headers.get? "host" |>.isSome)
  | .response => pure ()

  if let .request := ty then
    if req.method == .head ∨ req.method == .connect then
      return .fixed 0

  match (req.headers.get? "Content-Length", req.headers.hasEntry "Transfer-Encoding" "chunked") with
  | (some cl, false) => do
    let num ← cl.value.toNat?
    some (.fixed num)
  | (none, false) =>
    some (.fixed 0)
  | (none, true) =>
    some .chunked
  | (some _, true) =>
    some .chunked

private def processHeaders {ty : MachineType} (machine : Machine ty) : Machine ty :=
  let machine := updateKeepAlive machine

  match getMessageSize machine.reader.messageHead with
  | none =>
    machine.setFailure .badMessage
  | some size =>
    machine
    |>.addEvent (.endHeaders machine.reader.messageHead)
    |>.setReaderState <| match size with
      | .fixed n => .needFixedBody n
      | .chunked => .needChunkedSize

/--
Set message headers and determine transfer mode
-/
def setHeaders {ty : MachineType} (messageHead : MessageHead ty.swap) (machine : Machine ty) : Machine ty :=
  let size := Writer.determineBodySize machine.writer

  let headers := match ty with
    | .request =>
      if let some server := machine.config.identityHeader then
        messageHead.headers.insert "Server" server
      else
        messageHead.headers
    | .response =>
      if let some userAgent := machine.config.identityHeader then
        messageHead.headers.insert "User-Agent" userAgent
      else
        messageHead.headers

  let headers :=
    if let some date := machine.instant then
      let date := date.format "EEE, dd MMM yyyy HH:mm:ss 'GMT'"
      headers.insert "Date" (.ofString! date)
    else
      headers

  let headers := match ty, messageHead with
    | .request, messageHead => by
      exact if ¬machine.keepAlive ∨ shouldBreakConnection messageHead.status then
        headers.insert "Connection" (.new "close")
      else
        headers
    | .response, messageHead =>
      if ¬machine.keepAlive then
        headers.insert "Connection" (.new "close")
      else
        headers

  let headers := match size with
    | .fixed 0 => headers
    | .fixed n => headers.insert "Content-Length" (.ofString! <| toString n)
    | .chunked => headers.insert "Transfer-Encoding" (.new "chunked")

  let state := match size with
    | .fixed _ => Machine.Writer.State.writingFixedData
    | .chunked => Machine.Writer.State.writingChunkedBody

  let messageHead :=
    match ty, messageHead with
    | .request, messageHead => toString { messageHead with headers }
    | .response, messageHead => toString { messageHead with headers }

  machine.modifyWriter (fun writer => {
    writer with
    outputData := writer.outputData.append messageHead.toUTF8,
    state })

/--
Remove all the events in the machine
-/
@[inline]
def takeEvents (machine : Machine ty) : Machine ty × Array (Event ty) :=
  if machine.events.isEmpty then
    (machine, machine.events)
  else
    ({ machine with events := #[] }, machine.events)

/--
Put some data inside the input of the machine.
-/
@[inline]
def feed (machine : Machine ty) (data : ByteArray) : Machine ty :=
  { machine with reader := machine.reader.feed data }

/--
Set the current timestamp.
-/
@[inline]
def setNow (machine : Machine ty) : IO (Machine ty) := do
  return { machine with instant := some (← Std.Time.DateTime.now) }

/--
Put some data to be written.
-/
@[inline]
def writeUserData (machine : Machine ty) (data : ChunkedBuffer) : Machine ty :=
  { machine with writer := machine.writer.addUserData data }

/--
Put chunk extensions to be written.
-/
@[inline]
def writeChunkExt (machine : Machine ty) (chunkExt : Array (String × Option String)) : Machine ty :=
  { machine with writer := machine.writer.addChunkExt chunkExt }

/--
Close the writer.
-/
@[inline]
def closeWriter (machine : Machine ty) : Machine ty :=
  { machine with writer := machine.writer.close }

def isWriterOpened (machine : Machine ty) : Bool :=
  ¬machine.writer.closed

def isWaitingMessage (machine : Machine ty) : Bool :=
  match machine.writer.state with
  | .waitingHeaders => true
  | _ => false

/--
Sends the outgoing message
-/
def sendMessage {ty : MachineType} (machine : Machine ty) (messageHead : MessageHead ty.swap) : Machine ty :=
  match machine.writer.state with
  | .waitingHeaders =>
    let machine := machine.modifyWriter ({ · with messageHead := messageHead, state := .waitingForFlush })
    let headers := messageHead.headers
    let conn := headers.getLast? "Connection" |>.getD (.new "Keep-Alive")

    if conn.is "close" then
      machine
      |>.closeConnection
      |>.setReaderState .complete
    else
      machine

  | _ =>
    machine

def isReaderComplete {ty : MachineType} (machine : Machine ty) : Bool :=
  match machine.reader.state with
  | .complete => true
  | _ => false

def failed {ty : MachineType} (machine : Machine ty) : Bool :=
  match machine.reader.state with
  | .failed _ => true
  | _ => false

def shouldFlush {ty : MachineType} (machine : Machine ty) : Bool :=
  machine.failed ∨
  machine.writer.userData.size ≥ machine.config.highMark ∨
  machine.writer.closed

/--
Get the current output data and clear the buffer
-/
@[inline]
def takeOutput (machine : Machine ty) (highMark := 0) : Option (Machine ty × ChunkedBuffer) :=
  if machine.writer.outputData.size ≥ highMark ∨
    machine.writer.state == .complete
  then
    let output := machine.writer.outputData
    some ({ machine with writer := { machine.writer with outputData := .empty } }, output)
  else
    none

namespace Server

/--
Advances the state of the reader (for server/request mode).
-/
partial def processRead (machine : Machine .request) : Machine .request :=
  match machine.reader.state with
  | .needStartLine =>
    let (machine, result) := parseWith machine parseRequestLine (limit := some 8192)

    if let some head := result then
      if head.version != .v11 then
        machine
        |>.setFailure .unsupportedVersion
      else
        machine
        |>.modifyReader (.setMessageHead head)
        |>.setReaderState (.needHeader 0)
        |> processRead
    else
      machine

  | .needHeader headerCount =>
    let (machine, result) := parseWith machine (parseSingleHeader machine.config.maxHeaderSize) (limit := none)

    if headerCount > machine.config.maxHeaders then
      machine |>.setFailure .badMessage
    else
      if let some result := result then
        if let some (name, value) := result then
          if let some headerValue := HeaderValue.ofString? value then
            machine
            |>.modifyReader (.addHeader name headerValue)
            |>.setReaderState (.needHeader (headerCount + 1))
            |> processRead
          else
            machine.setFailure .badMessage
        else
          processHeaders machine
      else
        machine

  | .requireOutgoing _ =>
    machine

  | .needChunkedSize =>
    let (machine, result) := parseWith machine parseChunkSize (limit := some 128)

    match result with
    | some (size, ext) =>
      machine
      |>.setReaderState (.needChunkedBody size)
      |>.setEvent (some ext <&> .chunkExt)
      |> processRead
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
          |> processRead
        else
          machine
          |>.setReaderState .complete
          |>.addEvent (.gotData true .empty)
          |> processRead
      | .incomplete body remaining => machine
        |>.setReaderState (.needChunkedBody remaining)
        |>.addEvent (.gotData false body)
    else
      machine

  | .needFixedBody 0 =>
    machine
    |>.setReaderState .complete
    |>.addEvent (.gotData true .empty)
    |> processRead

  | .needFixedBody size =>
    let (machine, result) := parseWith machine (parseFixedSizeData size) (limit := none) (some size)

    if let some body := result then
      match body with
      | .complete body =>
        machine
        |>.setReaderState .complete
        |>.addEvent (.gotData true body)
        |> processRead
      | .incomplete body remaining =>
        machine
        |>.setReaderState (.needFixedBody remaining)
        |>.addEvent (.gotData false body)
    else
      machine

  | .complete =>
    machine

  | .failed _err =>
    machine
    |>.sendMessage { status := .badRequest }
    |>.resetAndClose
    |>.setReaderState .complete
    |>.closeConnection

/--
Write message data to the machine (for server/response mode)
-/
partial def processWrite (machine : Machine .request) : Machine .request :=
  match machine.writer.state with
  | .waitingHeaders =>
    machine

  | .waitingForFlush =>
    if machine.shouldFlush then
      machine.setHeaders machine.writer.messageHead |> processWrite
    else
      machine

  | .writingFixedData =>
    if machine.writer.userData.size ≥ machine.config.highMark ∨ machine.writer.closed then
      let machine := machine.modifyWriter Writer.writeFixedBody
      if machine.writer.closed then
        machine.setWriterState .complete |> processWrite
      else
        machine
    else
      machine

  | .writingChunkedBody =>
    if machine.writer.closed then
      machine.modifyWriter Writer.writeFinalChunk |> processWrite
    else if machine.writer.userData.size ≥ machine.config.highMark then
      machine.modifyWriter Writer.writeChunkedBody |> processWrite
    else
      machine

  | .complete =>
    resetForNextMessage machine

  | .writingHeaders =>
    machine

end Server

namespace Client

/--
Advances the state of the reader (for client/response mode).
-/
partial def processRead (machine : Machine .response) : Machine .response :=
  match machine.reader.state with
  | .needStartLine =>
    let (machine, result) := parseWith machine parseStatusLine (limit := some 8192)

    if let some head := result then
      if head.version != .v11 then
        machine
        |>.setFailure .unsupportedVersion
      else
        machine
        |>.modifyReader (.setMessageHead head)
        |>.setReaderState (.needHeader 0)
        |> processRead
    else
      machine

  | .needHeader headerCount =>
    let (machine, result) := parseWith machine (parseSingleHeader machine.config.maxHeaderSize) (limit := none)

    if headerCount > machine.config.maxHeaders then
      machine |>.setFailure .badMessage
    else
      if let some result := result then
        if let some (name, value) := result then
          if let some headerValue := HeaderValue.ofString? value then
            machine
            |>.modifyReader (.addHeader name headerValue)
            |>.setReaderState (.needHeader (headerCount + 1))
            |> processRead
          else
            machine.setFailure .badMessage
        else
          processHeaders machine
      else
        machine

  | .requireOutgoing _ =>
    machine

  | .needChunkedSize =>
    let (machine, result) := parseWith machine parseChunkSize (limit := some 128)

    match result with
    | some (size, ext) =>
      machine
      |>.setReaderState (.needChunkedBody size)
      |>.setEvent (some ext <&> .chunkExt)
      |> processRead
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
          |> processRead
        else
          machine
          |>.setReaderState .complete
          |>.addEvent (.gotData true .empty)
          |> processRead
      | .incomplete body remaining => machine
        |>.setReaderState (.needChunkedBody remaining)
        |>.addEvent (.gotData false body)
    else
      machine

  | .needFixedBody 0 =>
    machine
    |>.setReaderState .complete
    |>.addEvent (.gotData true .empty)
    |> processRead

  | .needFixedBody size =>
    let (machine, result) := parseWith machine (parseFixedSizeData size) (limit := none) (some size)

    if let some body := result then
      match body with
      | .complete body =>
        machine
        |>.setReaderState .complete
        |>.addEvent (.gotData true body)
        |> processRead
      | .incomplete body remaining =>
        machine
        |>.setReaderState (.needFixedBody remaining)
        |>.addEvent (.gotData false body)
    else
      machine

  | .complete =>
    machine

  | .failed _ =>
    machine
    |>.resetAndClose
    |>.setReaderState .complete
    |>.closeConnection

/--
Write message data to the machine (for client/request mode)
-/
partial def processWrite (machine : Machine .response) : Machine .response :=
  match machine.writer.state with
  | .waitingHeaders =>
    machine

  | .waitingForFlush =>
    if machine.shouldFlush then
      machine.setHeaders machine.writer.messageHead |> processWrite
    else
      machine

  | .writingFixedData =>
    if machine.writer.userData.size ≥ machine.config.highMark ∨ machine.writer.closed then
      let machine := machine.modifyWriter Writer.writeFixedBody
      if machine.writer.closed then
        machine.setWriterState .complete |> processWrite
      else
        machine
    else
      machine

  | .writingChunkedBody =>
    if machine.writer.closed then
      machine.modifyWriter Writer.writeFinalChunk |> processWrite
    else if machine.writer.userData.size ≥ machine.config.highMark then
      machine.modifyWriter Writer.writeChunkedBody |> processWrite
    else
      machine

  | .complete =>
    if machine.isReaderComplete then
      resetForNextMessage machine
    else
      machine

  | .writingHeaders =>
    machine

end Client
end Machine
