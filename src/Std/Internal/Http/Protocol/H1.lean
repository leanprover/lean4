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

/--
Results from a single step of the state machine.
-/
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
The HTTP 1.1 protocol state machine.
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
  keepAlive : Bool := false

  /--
  Whether a forced flush has been requested by the user.
  -/
  forcedFlush : Bool := false

  /--
  Host header.
  -/
  host : Option HeaderValue := none

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
private def setFailure (machine : Machine dir) (error : H1.Error) : Machine dir :=
  machine
  |>.addEvent (.failed error)
  |>.setReaderState (.failed error)
  |>.setError error

@[inline]
private def updateKeepAlive (machine : Machine dir) (should : Bool) : Machine dir :=
  { machine with keepAlive := should ∧ machine.reader.messageCount < machine.config.maxMessages }

-- Helper Functions

@[inline]
private def hasConnectionClose (headers : Headers) : Bool :=
  headers.getLast? (.new "Connection") |>.map (·.is "close") |>.getD false

@[inline]
def shouldKeepAlive (message : Message.Head dir) : Bool :=
  ¬message.headers.hasEntry (.new "Connection") "close" ∧ message.version = .v11

private def extractBodyLengthFromHeaders (headers : Headers) : Option Body.Length :=
  match (headers.get (.new "Content-Length"), headers.hasEntry (.new "Transfer-Encoding") "chunked") with
  | (some cl, false) => cl.value.toNat? >>= (some ∘ Body.Length.fixed)
  | (none, true) => some Body.Length.chunked
  | (some _, true) => some Body.Length.chunked
  | _ => none

def getMessageSize (req : Message.Head dir) : Option Body.Length := do
  match dir with
  | .receiving => guard (req.headers.get (.new "host") |>.isSome)
  | .sending => pure ()

  if let .receiving := dir then
    if req.method == .head ∨ req.method == .connect then
      return .fixed 0

  match (req.headers.get (.new "Content-Length"), req.headers.hasEntry (.new "Transfer-Encoding") "chunked") with
  | (some cl, false) => do
    let num ← cl.value.toNat?
    some (.fixed num)
  | (none, false) => some (.fixed 0)
  | (none, true) => some .chunked
  | (some _, true) => some .chunked

-- State Checks

@[inline]
def failed (machine : Machine dir) : Bool :=
  match machine.reader.state with
  | .failed _ => true
  | _ => false

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

@[inline]
def shouldFlush (machine : Machine dir) : Bool :=
  machine.failed ∨
  machine.reader.state == .closed ∨
  machine.writer.isReadyToSend ∨
  machine.writer.knownSize.isSome

@[inline]
def isWaitingMessage (machine : Machine dir) : Bool :=
  machine.writer.state == .waitingHeaders ∧
  ¬machine.writer.sentMessage

@[inline]
def halted (machine : Machine dir) : Bool :=
  match machine.reader.state, machine.writer.state with
  | .closed, .closed => machine.writer.outputData.isEmpty
  | _, _ => false

private def parseWith (machine : Machine dir) (parser : Parser α) (limit : Option Nat)
    (expect : Option Nat := none) : Machine dir × Option α :=
  let remaining := machine.reader.input.remainingBytes
  match parser machine.reader.input with
  | .success buffer result =>
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
        canSendData := true,
        sentMessage := false
      },
      events := machine.events.push .next,
      error := none
    }
  else
    machine.addEvent .close

private def processHeaders (machine : Machine dir) : Machine dir :=
  let shouldKeepAlive := shouldKeepAlive machine.reader.messageHead
  let hasClose := hasConnectionClose machine.reader.messageHead.headers

  let machine := updateKeepAlive machine (shouldKeepAlive ∧ ¬hasClose)

  match getMessageSize machine.reader.messageHead with
  | none => machine.setFailure .badMessage
  | some size =>
      let machine := machine.addEvent (.endHeaders machine.reader.messageHead)
      let machine := if hasClose then { machine with keepAlive := false } else machine

      machine.setReaderState <| match size with
        | .fixed n => .needFixedBody n
        | .chunked => .needChunkedSize

def setHeaders (messageHead : Message.Head dir.swap) (machine : Machine dir) : Machine dir :=
  let hasClose := hasConnectionClose messageHead.headers
  let machine := { machine with keepAlive := ¬hasClose }
  let size := Writer.determineTransferMode machine.writer

  let headers :=
    if messageHead.headers.contains (.new "host") then
      messageHead.headers
    else if let some host := machine.host then
      messageHead.headers.insert (.new "Host") host
    else
      messageHead.headers

  -- Add identity header based on direction
  let headers :=
    let identityOpt := machine.config.identityHeader
    match dir, identityOpt with
    | .receiving, some server => headers.insert (.new "Server") server
    | .sending, some userAgent => headers.insert (.new "User-Agent") userAgent
    | _, none => headers

  -- Add Connection: close if needed
  let headers :=
    if !machine.keepAlive ∧ !headers.hasEntry (.new "Connection") "close" then
      headers.insert (.new "Connection") (.new "close")
    else
      headers

  -- Add Content-Length or Transfer-Encoding if needed
  let headers :=
    if !(headers.contains (.new "Content-Length") ∨ headers.contains (.new "Transfer-Encoding")) then
      match size with
      | .fixed n => headers.insert (.new "Content-Length") (.ofString! <| toString n)
      | .chunked => headers.insert (.new "Transfer-Encoding") (.new "chunked")
    else
      headers

  let state := Writer.State.writingBody size

  let messageHead :=
    match dir, messageHead with
    | .receiving, messageHead => toString { messageHead with headers }
    | .sending, messageHead => toString { messageHead with headers }

  machine.modifyWriter (fun writer => {
    writer with
    outputData := writer.outputData.append messageHead.toUTF8,
    state
  })

/-- Put some data inside the input of the machine. -/
@[inline]
def feed (machine : Machine ty) (data : ByteArray) : Machine ty :=
  { machine with reader := machine.reader.feed data }

/-- Signal that reader is not going to receive any more messages. -/
@[inline]
def closeReader (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with noMoreInput := true })

/-- Signal that the writer cannot send more messages because the socket closed. -/
@[inline]
def closeWriter (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with canSendData := false })

/-- Signal that the user is not sending data anymore. -/
@[inline]
def userClosedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userClosedBody := true })

/-- Signal that the socket is not sending data anymore. -/
@[inline]
def noMoreInput (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with noMoreInput := true })

/-- Set a known size for the message body. -/
@[inline]
def setKnownSize (machine : Machine dir) (size : Body.Length) : Machine dir :=
  machine.modifyWriter (fun w => { w with knownSize := w.knownSize.or (some size) })

/-- Send the head of a message to the machine. -/
@[inline]
def send (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  if machine.isWaitingMessage then
    let machine := machine.modifyWriter ({ · with messageHead := message, sentMessage := true })
    let machine := machine.updateKeepAlive (shouldKeepAlive message)

    let machine :=
      if machine.writer.knownSize.isNone then
        match extractBodyLengthFromHeaders message.headers with
        | some size => machine.setKnownSize size
        | none => machine
      else
        machine

    machine.setWriterState .waitingForFlush
  else
    machine

/-- Send data to the socket. -/
@[inline]
def sendData (machine : Machine dir) (data : Array Chunk) : Machine dir :=
  if data.isEmpty then
    machine
  else
    machine.modifyWriter (fun writer => { writer with userData := writer.userData ++ data })

/-- Get all the events of the machine. -/
@[inline]
def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/-- Take all the accumulated output to send to the socket. -/
@[inline]
def takeOutput (machine : Machine dir) : Machine dir × ChunkedBuffer :=
  let output := machine.writer.outputData
  ({ machine with writer := { machine.writer with outputData := .empty } }, output)

/-- Signal that it can start receiving another request. -/
@[inline]
def startNextCycle (machine : Machine dir) : Machine dir :=
  if machine.keepAlive &&
     machine.reader.state == .complete &&
     machine.writer.state == .complete then
    resetForNextMessage machine
  else
    machine

/-- Process the writer part of the machine. -/
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

  | .writingBody (.fixed n) =>
      if machine.writer.userData.size > 0 ∨ machine.writer.isReadyToSend then
        let (writer, remaining) := Writer.writeFixedBody machine.writer n
        let machine := { machine with writer }

        if machine.writer.isReadyToSend ∨ remaining = 0 then
          machine.setWriterState .complete |> processWrite
        else
          machine.setWriterState (.writingBody (.fixed remaining))
      else
        machine

  | .writingBody .chunked =>
      if machine.writer.userClosedBody then
        machine.modifyWriter Writer.writeFinalChunk
        |>.setWriterState .complete
        |> processWrite
      else if machine.writer.userData.size > 0 ∨ machine.writer.isReadyToSend then
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

/-- Handle the failed state for the reader. -/
private def handleReaderFailed (machine : Machine dir) (error : H1.Error) : Machine dir :=
  let machine : Machine dir :=
    match dir with
    | .receiving => machine |>.send { status := .badRequest } |>.userClosedBody
    | .sending => machine

  machine
  |>.setReaderState .closed
  |>.addEvent (.failed error)
  |>.setError error
  |>.disableKeepAlive

/-- Process the reader part of the machine. -/
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
          | .receiving => parseWith machine (parseRequestLine machine.config) (limit := some 8192)
          | .sending => parseWith machine (parseStatusLine machine.config) (limit := some 8192)

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
      let (machine, result) := parseWith machine
        (parseSingleHeader machine.config) (limit := none)

      if headerCount > machine.config.maxHeaders then
        machine |>.setFailure .badMessage
      else
        if let some result := result then
          if let some (name, value) := result then
            if let some (name, headerValue) := Prod.mk <$> HeaderName.ofString? name <*> HeaderValue.ofString? value then
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
      let (machine, result) := parseWith machine (parseChunkSize machine.config) (limit := some 128)

      match result with
      | some (size, ext) =>
          machine
          |>.setReaderState (.needChunkedBody size)
          |>.setEvent (some ext <&> .chunkExt)
          |> processRead
      | none =>
          machine

  | .needChunkedBody size =>
      let (machine, result) := parseWith machine
        (parseChunkedSizedData size) (limit := none) (some size)

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
        | .incomplete body remaining =>
            machine
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

/-- Execute one step of the state machine. -/
def step (machine : Machine dir) : Machine dir × StepResult dir :=
  let machine := machine.processRead.processWrite
  let (machine, events) := machine.takeEvents
  let (machine, output) := machine.takeOutput
  (machine, { events, output })

end Std.Http.Protocol.H1.Machine
