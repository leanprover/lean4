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

namespace Std.Http.Protocol.H1

open Std Internal Parsec ByteArray
open Internal

structure StepResult (dir : Direction) where
  /--
  Events that occurred during this step (e.g., headers received, data available, errors).
  -/
  events : Array (Event dir) := #[]

  /--
  Output data ready to be sent to the socket.
  -/
  output : ChunkedBuffer := .empty

/--
The state machine that receives some input bytes and outputs bytes for the HTTP 1.1 protocol.
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
  The configuration of the
  -/
  config : Config

  /--
  Events that happened during reading and writing.
  -/
  events : Array (Event dir) := #[]

  /--
  Error thrown by the machine
  -/
  error : Option Error := none

  /--
  The timestamp that will be used to create the `Date` header.
  -/
  instant : Option (Std.Time.DateTime .UTC) := none

  /--
  If the connection will be kept alive after the message.
  -/
  keepAlive : Bool := false

  /--

  -/
  forcedFlush : Bool := false

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
private def setEvent (machine : Machine dir) (event : Option (Event dir)) : Machine dir :=
  match event with
  | some event => machine.addEvent event
  | none => machine

@[inline]
private def setError (machine : Machine dir) (error : Error) : Machine dir :=
  { machine with error := some error }

@[inline]
private def disableKeepAlive (machine : Machine dir) : Machine dir :=
  { machine with keepAlive := false }

@[inline]
private def hasConnectionClose (headers : Headers) : Bool :=
  headers.getLast? "Connection" |>.map (·.is "close") |>.getD false

@[inline]
private def setFailure (machine : Machine dir) (error : H1.Error) : Machine dir :=
  machine
  |>.addEvent (.failed error)
  |>.setReaderState (.failed error)
  |>.setError error

private def resetForNextMessage (machine : Machine ty) : Machine ty :=
  let newMessageCount := machine.reader.messageCount + 1
  let shouldKeepAlive := machine.keepAlive && newMessageCount < machine.config.maxMessages

  if shouldKeepAlive then
    { machine with
      reader := {
        state := .needStartLine,
        input := machine.reader.input,
        messageHead := {},
        messageCount := newMessageCount
      },
      writer := {
        userData := .empty,
        outputData := machine.writer.outputData,
        state := .waitingHeaders,
        knownSize := none,
        messageHead := {},
        userClosedBody := false,
        transferMode := none,
        canSendData := true,
        sentMessage := false
      },
      events := machine.events.push .next,
      error := none,
      instant := none
    }
  else
    machine.addEvent .close

private def parseWith (machine : Machine dir) (parser : Parser α) (limit : Option Nat) (expect : Option Nat := none) : Machine dir × Option α :=
  let remaining := machine.reader.input.remainingBytes
    match parser machine.reader.input with
  | .success buffer result => ({ machine with reader := machine.reader.setInput buffer }, some result)
  | .error it .eof =>
    let usedBytesUntilFailure := remaining - it.remainingBytes

    -- If connection is closed by peer, trigger connectionClosed error instead of needMoreData
    if machine.reader.noMoreInput then
      (machine.setFailure .connectionClosed, none)
    else if let some limit := limit then
      if usedBytesUntilFailure ≥ limit
        then (machine.setFailure .badMessage, none)
        else (machine.addEvent (.needMoreData expect), none)
    else (machine.addEvent (.needMoreData expect), none)
  | .error _ _ => (machine.setFailure .badMessage, none)

@[inline]
def shouldKeepAlive (message : Message.Head dir) : Bool :=
  ¬message.headers.hasEntry "Connection" "close"

def getMessageSize (req : Message.Head dir) : Option Body.Length := do
  match dir with
  | .receiving => guard (req.headers.get "host" |>.isSome)
  | .sending => pure ()

  if let .receiving := dir then
    if req.method == .head ∨ req.method == .connect then
      return .fixed 0

  match (req.headers.get "Content-Length", req.headers.hasEntry "Transfer-Encoding" "chunked") with
  | (some cl, false) => do
    let num ← cl.value.toNat?
    some (.fixed num)
  | (none, false) =>
    some (.fixed 0)
  | (none, true) =>
    some .chunked
  | (some _, true) =>
    some .chunked

@[inline]
private def updateKeepAlive (machine : Machine dir) (should : Bool) : Machine dir :=
  { machine with keepAlive := should ∧ machine.reader.messageCount < machine.config.maxMessages }

private def processHeaders (machine : Machine dir) : Machine dir :=
  let shouldKeepAlive := shouldKeepAlive machine.reader.messageHead
  let hasClose := hasConnectionClose machine.reader.messageHead.headers

  let machine := updateKeepAlive machine (shouldKeepAlive ∧ ¬hasClose)

  match getMessageSize machine.reader.messageHead with
  | none => machine.setFailure .badMessage
  | some size =>
    let machine := machine.addEvent (.endHeaders machine.reader.messageHead)

    let machine := if hasClose then
      { machine with keepAlive := false }
    else
      machine

    machine.setReaderState <| match size with
      | .fixed n => .needFixedBody n
      | .chunked => .needChunkedSize


def setHeaders (messageHead : Message.Head dir.swap) (machine : Machine dir) : Machine dir :=
  let hasClose := hasConnectionClose messageHead.headers

  let machine := { machine with keepAlive := ¬hasClose }

  let size := Writer.determineTransferMode machine.writer

  let headers := match dir with
    | .receiving =>
      if let some server := machine.config.identityHeader then
        messageHead.headers.insert "Server" server
      else
        messageHead.headers
    | .sending =>
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

  let headers := match dir, messageHead with
    | .receiving, messageHead => by
      exact if ¬machine.keepAlive ∧ ¬headers.hasEntry "Connection" "close" then
        headers.insert "Connection" (.new "close")
      else
        headers
    | .sending, messageHead =>
      if ¬machine.keepAlive ∧ ¬headers.hasEntry "Connection" "close" then
        headers.insert "Connection" (.new "close")
      else
        headers

  let headers := match size with
    | .fixed 0 => headers
    | .fixed n => headers.insert "Content-Length" (.ofString! <| toString n)
    | .chunked => headers.insert "Transfer-Encoding" (.new "chunked")

  let state := Writer.State.writingBody size

  let messageHead :=
    match dir, messageHead with
    | .receiving, messageHead => toString { messageHead with headers }
    | .sending, messageHead => toString { messageHead with headers }

  machine.modifyWriter (fun writer => {
    writer with
    outputData := writer.outputData.append messageHead.toUTF8,
    state })

def failed (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .failed _ => true
  | _ => false

def shouldFlush (machine : Machine dir) : Bool :=
  machine.failed ∨
  machine.reader.state == .closed ∨
  machine.writer.userData.size ≥ machine.config.highMark ∨
  machine.writer.isReadyToSend

@[inline]
def isReaderComplete (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .complete => true
  | _ => false

@[inline]
def isReaderClosed (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .closed => true
  | _ => false

-- Public functions

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
This functions signals that reader is not going to receive any more messages, so it signals that the
writer can flush the data and close the machine.
-/
@[inline]
def closeReader (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with noMoreInput := true })

/--
This function signals that the writer is not able to send more messages because the socket closed it's
connection.
-/
@[inline]
def closeWriter (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with canSendData := false })

/--
Signals to the writer that the user is not sending data anymore. It's useful to determine the size of the
payload.
-/
@[inline]
def userClosedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userClosedBody := true })

/--
Signals to the writer that the socket is not sending data anymore.
-/
@[inline]
def noMoreInput (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with noMoreInput := true })

/--
Checks if the machine halted.
-/
@[inline]
def halted (machine : Machine dir) : Bool :=
  match machine.reader.state, machine.writer.state with
  | .closed, .closed => machine.writer.outputData.isEmpty
  | _, _ => false

/--
Sends the head of an answer to the machine.
-/
@[inline]
def isWaitingMessage (machine : Machine dir) : Bool :=
  machine.writer.state == .waitingHeaders ∧
  ¬machine.writer.sentMessage

/--
Sends the head of an answer to the machine.
-/
@[inline]
def send (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  if machine.isWaitingMessage then
    let machine := machine.modifyWriter ({ · with messageHead := message, sentMessage := true })
    let machine := machine.updateKeepAlive (shouldKeepAlive message)
    machine.setWriterState .waitingForFlush
  else
    machine

/--
Sends the data to the socket.
-/
@[inline]
def sendData (machine : Machine dir) (data : Array Chunk)  : Machine dir :=
  if data.isEmpty then
    machine
  else
    machine.modifyWriter (fun writer => { writer with userData := writer.userData ++ data })

/--
Gets all the events of the machine
-/
@[inline]
def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/--
Takes all the accumulated output to send to the socket.
-/
@[inline]
def takeOutput (machine : Machine dir) : Machine dir × ChunkedBuffer :=
  let output := machine.writer.outputData
  ({ machine with writer := { machine.writer with outputData := .empty } }, output)

/--
Signals that it can start sending receiving another request.
-/
@[inline]
def startNextCycle (machine : Machine dir) : Machine dir :=
  if machine.keepAlive &&
     machine.reader.state == .complete &&
     machine.writer.state == .complete then
    resetForNextMessage machine
  else
    machine

/--
Set a known size for the message body.
-/
@[inline]
def setKnownSize (machine : Machine dir) (size : Nat) : Machine dir :=
  machine.modifyWriter ({ · with knownSize := some size })

/--
?
-/
@[inline]
def needsInput (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .needStartLine | .needHeader _ | .needChunkedSize
  | .needChunkedBody _ | .needFixedBody _ => true
  | _ => false

/--
?
-/
@[inline]
def canAcceptResponse (machine : Machine dir) : Bool :=
  machine.writer.state == .waitingHeaders

/--
?
-/
@[inline]
def isProcessingRequest (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .closed | .complete | .failed _ => false
  | _ => true

/--
?
-/
@[inline]
def requiresResponse (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .needStartLine | .closed | .complete => false
  | _ => true
/--
?
-/
@[inline]
def needsOutputFlush (machine : Machine dir) : Bool :=
  ¬machine.writer.outputData.isEmpty ∨
  machine.writer.userData.size ≥ machine.config.highMark

/--
This function processes the writer part of the machine.
-/
partial def processWrite (machine : Machine dir) : Machine dir :=
  match machine.writer.state with
  | .waitingHeaders =>
    if ¬machine.writer.canSendData then
      machine.setWriterState .closed
    else
      machine

  | .waitingForFlush =>
    if machine.shouldFlush then
      machine.setHeaders machine.writer.messageHead
      |> processWrite
    else
      machine

  | .writingHeaders =>
    machine.setWriterState (.writingBody (Writer.determineTransferMode machine.writer))
    |> processWrite

  | .writingBody (.fixed _) =>
    if machine.writer.userData.size ≥ machine.config.highMark ∨ machine.writer.isReadyToSend then
      let machine := machine.modifyWriter Writer.writeFixedBody
      if machine.writer.isReadyToSend then
        machine.setWriterState .complete |> processWrite
      else
        machine
    else
      machine

  | .writingBody .chunked =>
    if machine.writer.userClosedBody then
      machine.modifyWriter Writer.writeFinalChunk
      |>.setWriterState .complete
      |> processWrite
    else if machine.writer.userData.size >= machine.config.highMark ∨ machine.writer.isReadyToSend then
      machine.modifyWriter Writer.writeChunkedBody
      |> processWrite
    else
      machine

  | .shuttingDown =>
    if machine.writer.outputData.isEmpty then
      machine.setWriterState .complete |> processWrite
    else
      machine

  | .complete =>
    if machine.isReaderComplete then
      if machine.keepAlive then
        resetForNextMessage machine
      else
        machine.setWriterState .closed
        |>.addEvent .close
    else if machine.isReaderClosed then
      machine.setWriterState .closed
      |>.addEvent .close
    else
      if machine.keepAlive then
        machine
      else
        machine.setWriterState .closed
  | .closed =>
    machine

/--
The failed state handler for the reader.
-/
private def handleReaderFailed (machine : Machine dir) (error : H1.Error) : Machine dir :=

  let machine : Machine dir :=
    match dir, machine with
    | .receiving, machine => machine |>.send { status := .badRequest } |>.userClosedBody
    | .sending, machine => machine

  machine
  |>.setReaderState .closed
  |>.addEvent (.failed error)
  |>.setError error
  |>.disableKeepAlive

/--
Complete the processRead function's failed case.
-/
partial def processRead (machine : Machine dir) : Machine dir :=
  match machine.reader.state with
  | .needStartLine =>
    if machine.reader.noMoreInput ∧ machine.reader.input.atEnd then
      machine.setReaderState .closed
    else if machine.reader.input.atEnd then
      machine.addEvent (.needMoreData none)
    else
      let (machine, result) : Machine dir × Option (Message.Head dir) :=
        match dir with
        | .receiving => parseWith machine parseRequestLine (limit := some 8192)
        | .sending => parseWith machine parseStatusLine (limit := some 8192)

      if let some head := result then
        if head.version != .v11 then
          machine.setFailure .unsupportedVersion
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

  | .requireOutgoing _ =>
    machine

  | .complete =>
    if ¬machine.keepAlive then
      machine.setReaderState .closed
    else
      machine
  | .closed =>
    machine

  | .failed error =>
    handleReaderFailed machine error

def step (machine : Machine dir) : Machine dir × StepResult dir :=
  let machine := machine.processRead.processWrite
  let (machine, events) := machine.takeEvents
  let (machine, output) := machine.takeOutput
  (machine, { events, output })

end Std.Http.Protocol.H1.Machine
