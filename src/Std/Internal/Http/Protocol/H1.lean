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
  { machine with keepAlive := machine.keepAlive ∧ should }


private inductive BodyMode where
  | fixed (n : Nat)
  | chunked
  | eof

@[inline]
private def responseMustNotHaveBody (status : Status) : Bool :=
  let code := status.toCode.toNat
  (100 ≤ code ∧ code < 200) ∨ code = 204 ∨ code = 304

private def checkMessageHead (message : Message.Head dir) : Option BodyMode := do
  match dir with
  | .receiving => do
    let headers ← message.headers.getAll? Header.Name.host
    guard (headers.size = 1)
    let size ← message.getSize true
    match size with
    | .fixed n => return .fixed n
    | .chunked => return .chunked
  | .sending => pure ()

  if let .sending := dir then
    match message.getSize false with
    | some (.fixed n) => return .fixed n
    | some .chunked => return .chunked
    | none =>
        if message.headers.contains Header.Name.contentLength ∨ message.headers.contains Header.Name.transferEncoding then
          none
        else if responseMustNotHaveBody message.status then
          some (.fixed 0)
        else
          some .eof
  else
    none

@[inline]
private def hasExpectContinue (message : Message.Head dir) : Bool :=
  match message.headers.getAll? Header.Name.expect with
  | none => false
  | some values =>
      values.any fun value =>
        value.value.split (· == ',')
        |>.any (fun token => token.trimAscii.toString.toLower == "100-continue")

@[inline]
private def shouldIgnoreBodyPull (machine : Machine dir) : Bool :=
  match dir with
  | .receiving => machine.writer.sentMessage
  | .sending => false

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
  machine.writer.knownSize.isSome

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

private def resetForNextMessage (machine : Machine ty) : Machine ty :=

  if machine.keepAlive then
    { machine with
      reader := {
        state := .needStartLine,
        input := machine.reader.input,
        messageHead := {},
        messageCount := machine.reader.messageCount + 1
      },
      writer := {
        userData := .empty,
        outputData := machine.writer.outputData,
        state := .pending,
        knownSize := none,
        messageHead := {},
        userClosedBody := false,
        sentMessage := false
      },
      events := machine.events.push .next,
      error := none,
      pullBodyStalled := false
    }
  else
    machine.addEvent .close
    |>.setWriterState .closed
    |>.setReaderState .closed

/-
This function processes the message we are receiving
-/
private def processHeaders (machine : Machine dir) : Machine dir :=
  let machine := machine.updateKeepAlive (machine.reader.messageCount + 1 < machine.config.maxMessages)

  let shouldKeepAlive : Bool := machine.reader.messageHead.shouldKeepAlive
  let machine := updateKeepAlive machine shouldKeepAlive

  match checkMessageHead machine.reader.messageHead with
  | none => machine.setFailure .badMessage
  | some mode =>
      let (machine, state) : Machine dir × Reader.State dir := match mode with
      | .fixed n => (machine, Reader.State.readBody (.fixed n))
      | .chunked => (machine, Reader.State.readBody .chunkedSize)
      | .eof => (machine.disableKeepAlive, Reader.State.readBody .closeDelimited)

      let machine := machine.addEvent (.endHeaders machine.reader.messageHead)

      let waitingContinue : Bool :=
        match dir with
        | .receiving => hasExpectContinue machine.reader.messageHead
        | .sending => false

      let nextState : Reader.State dir := if waitingContinue then Reader.State.«continue» state else state
      let machine := if waitingContinue then machine.addEvent .continue else machine

      let machine := machine.setReaderState nextState
        |>.setWriterState .waitingHeaders
        |>.addEvent .needAnswer
      machine

/--
This processes the message we are sending.
-/
def setHeaders (messageHead : Message.Head dir.swap) (machine : Machine dir) : Machine dir :=
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

  -- Normalize framing to a single authoritative header.
  let headers :=
    let headers := headers.erase Header.Name.contentLength |>.erase Header.Name.transferEncoding
    match size with
    | .fixed n => headers.insert Header.Name.contentLength (.ofString! <| toString n)
    | .chunked => headers.insert Header.Name.transferEncoding Header.Value.chunked

  let state := Writer.State.writingBody size

  machine.modifyWriter (fun writer => {
    writer with

    outputData :=
      match dir, messageHead with
      | .receiving, messageHead => Encode.encode (v := .v11) writer.outputData { messageHead with headers }
      | .sending, messageHead => Encode.encode  (v := .v11) writer.outputData { messageHead with headers },

    state
  })

/-- Feeds input bytes into the reader side of the machine. -/
@[inline]
def feed (machine : Machine ty) (data : ByteArray) : Machine ty :=
  if machine.isReaderClosed then
    machine
  else
    { machine with reader := machine.reader.feed data, pullBodyStalled := false }

/-- Signals that the reader will not receive any more input bytes. -/
@[inline]
def closeReader (machine : Machine dir) : Machine dir :=
  machine.modifyReader ({ · with noMoreInput := true })

/-- Signal that the writer cannot send more messages because the socket closed. -/
@[inline]
def closeWriter (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with state := .closed, userClosedBody := true })

/-- Signal that the user is not sending data anymore. -/
@[inline]
def userClosedBody (machine : Machine dir) : Machine dir :=
  machine.modifyWriter ({ · with userClosedBody := true })

/-- Signal that the socket is not sending data anymore. -/
@[inline]
def noMoreInput (machine : Machine dir) : Machine dir :=
  { machine.modifyReader ({ · with noMoreInput := true }) with pullBodyStalled := false }

/-- Set a known size for the message body, replacing any previous value. -/
@[inline]
def setKnownSize (machine : Machine dir) (size : Body.Length) : Machine dir :=
  machine.modifyWriter (fun w => { w with knownSize := some size })

/-- Send the head of a message to the machine. -/
@[inline]
def send (machine : Machine dir) (message : Message.Head dir.swap) : Machine dir :=
  if machine.isWaitingMessage then
    let machine := machine.modifyWriter ({ · with messageHead := message, sentMessage := true })
    let framingInHeaders :=
      message.headers.contains Header.Name.contentLength ∨
      message.headers.contains Header.Name.transferEncoding
    let headerSize := message.getSize false

    let machine :=
      match machine.writer.knownSize, headerSize with
      | some explicit, some parsed =>
          if explicit == parsed then
            machine
          else
            machine.setFailure .badMessage
      | some _, none =>
          if framingInHeaders then
            machine.setFailure .badMessage
          else
            machine
      | none, some parsed =>
          machine.setKnownSize parsed
      | none, none =>
          if framingInHeaders then
            machine.setFailure .badMessage
          else
            machine

    if machine.failed then
      machine
    else
      machine.setWriterState .waitingForFlush
  else
    machine

/--
Allow body processing to continue after receiving `Expect: 100-continue`.
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

/--Send data to the socket. -/
@[inline]
def sendData (machine : Machine dir) (data : Array Chunk) : Machine dir :=
  if data.isEmpty then
    machine
  else
    machine.modifyWriter (fun writer => { writer with userData := writer.userData ++ data })

/--Get all the events of the machine. -/
@[inline]
def takeEvents (machine : Machine dir) : Machine dir × Array (Event dir) :=
  ({ machine with events := #[] }, machine.events)

/--Take all the accumulated output to send to the socket. -/
@[inline]
def takeOutput (machine : Machine dir) : Machine dir × ChunkedBuffer :=
  let output := machine.writer.outputData
  ({ machine with writer := { machine.writer with outputData := .empty } }, output)

/--Process the writer part of the machine. -/
partial def processWrite (machine : Machine dir) : Machine dir :=
  match machine.writer.state with
  | .pending =>
      if machine.reader.isClosed then
        machine.closeWriter
      else
        machine
  | .waitingHeaders =>
      machine.addEvent .needAnswer
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
      if n = 0 then
        if machine.writer.userData.isEmpty then
          machine.setWriterState .complete |> processWrite
        else
          machine
          |>.disableKeepAlive
          |>.setWriterState .closed
          |>.addEvent .close
      else if machine.writer.userData.size > 0 then
        let (writer, remaining) := Writer.writeFixedBody machine.writer n
        let machine := { machine with writer }

        if remaining = 0 then
          machine.setWriterState .complete |> processWrite
        else
          machine.setWriterState (.writingBody (.fixed remaining))
      else if machine.writer.userClosedBody then
        machine
        |>.disableKeepAlive
        |>.setWriterState .closed
        |>.addEvent .close
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
private def errorResponseStatus (error : H1.Error) : Status :=
  match error with
  | .unsupportedVersion => .httpVersionNotSupported
  | .entityTooLarge => .payloadTooLarge
  | .unsupportedMethod => .notImplemented
  | _ => .badRequest

/-- Handle the failed state for the reader. -/
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
Parse body bytes according to the current body framing state.
Returns the updated machine, an optional pulled chunk, and whether processing
should continue immediately.
-/
private def parseBody (machine : Machine dir) (bodyState : Reader.BodyState) :
    Machine dir × Option PulledChunk × Bool :=
  match bodyState with
  | .fixed 0 =>
      let machine := machine
        |>.setReaderState .complete
        |>.addEvent .closeBody
      (machine, mkPulledChunk? machine true false #[] .empty, true)

  | .fixed size =>
      let (machine, result) := parseWith machine (parseFixedSizeData size) (limit := none) (some size)
      match result with
      | some (.complete body) =>
          let machine := machine
            |>.setReaderState .complete
            |>.addEvent .closeBody
          (machine, mkPulledChunk? machine true false #[] body, true)
      | some (.incomplete body remaining) =>
          let machine := machine.setReaderState (.readBody (.fixed remaining))
          (machine, mkPulledChunk? machine false true #[] body, true)
      | none =>
          (machine, none, false)

  | .chunkedSize =>
      let (machine, result) := parseWith machine
        (parseChunkSize machine.config)
        (limit := some machine.config.maxChunkLineLength)
      match result with
      | some (size, ext) =>
          if size > machine.config.maxChunkSize then
            (machine.setFailure .entityTooLarge, none, false)
          else
            (machine.setReaderState (.readBody (.chunkedBody ext size)), none, true)
      | none =>
          (machine, none, false)

  | .chunkedBody ext 0 =>
      let (machine, result) := parseWith machine (parseLastChunkBody machine.config) (limit := some 2)
      match result with
      | some _ =>
          let machine := machine
            |>.setReaderState .complete
            |>.addEvent .closeBody
          (machine, mkPulledChunk? machine true false ext .empty, true)
      | none =>
          (machine, none, false)

  | .chunkedBody ext size =>
      let (machine, result) := parseWith machine (parseChunkSizedData size) (limit := none) (some size)
      match result with
      | some (.complete body) =>
          let machine := machine.setReaderState (.readBody .chunkedSize)
          (machine, mkPulledChunk? machine false false ext body, true)
      | some (.incomplete body remaining) =>
          let machine := machine.setReaderState (.readBody (.chunkedBody ext remaining))
          (machine, mkPulledChunk? machine false true ext body, true)
      | none =>
          (machine, none, false)

  | .closeDelimited =>
      if machine.reader.input.atEnd then
        if machine.reader.noMoreInput then
          let machine := machine
            |>.setReaderState Reader.State.complete
            |>.addEvent .closeBody
          (machine, mkPulledChunk? machine true false #[] .empty, true)
        else
          (machine.addEvent (.needMoreData none), none, false)
      else
        let data := machine.reader.input.array[machine.reader.input.pos...machine.reader.input.array.size]
        let machine := machine
          |>.modifyReader (fun r => r.advance r.remainingBytes)
          |>.setReaderState (.readBody .closeDelimited)
        (machine, mkPulledChunk? machine false false #[] data, true)

/--Process the reader part of the machine. -/
partial def processRead (machine : Machine dir) : Machine dir :=
  match machine.reader.state with
  | .needStartLine =>
      if machine.reader.noMoreInput ∧ machine.reader.input.atEnd then
        machine.setReaderState .closed
      else if machine.reader.input.atEnd then
        machine.addEvent (.needMoreData none)
      else
        match dir with
        | .receiving =>
            let (machine, result) := parseWith machine
              (parseRequestLineRawVersion machine.config)
              (limit := some machine.config.maxStartLineLength)
            if let some (method, uri, version) := result then
              if version == some .v11 then
                machine
                |>.modifyReader (.setMessageHead ({ method, version := .v11, uri, headers := .empty } : Request.Head))
                |>.setReaderState (.needHeader 0)
                |> processRead
              else
                machine.setFailure .unsupportedVersion
            else
              machine
        | .sending =>
            let (machine, result) := parseWith machine
              (parseStatusLineRawVersion machine.config)
              (limit := some machine.config.maxStartLineLength)
            if let some (status, reasonPhrase, version) := result then
              if version == some .v11 then
                machine
                |>.modifyReader (.setMessageHead ({
                  status,
                  reasonPhrase := some reasonPhrase,
                  version := .v11,
                  headers := .empty
                } : Response.Head))
                |>.setReaderState (.needHeader 0)
                |> processRead
              else
                machine.setFailure .unsupportedVersion
            else
              machine

  | .needHeader headerCount =>
      let (machine, result) := parseWith machine
        (parseSingleHeader machine.config) (limit := none)
      if let some result := result then
        if let some (name, value) := result then
          if headerCount ≥ machine.config.maxHeaders then
            machine.setFailure .badMessage
          else if let some (name, headerValue) := Prod.mk <$> Header.Name.ofString? name <*> Header.Value.ofString? value then
            machine
            |>.modifyReader (.addHeader name headerValue)
            |>.setReaderState (.needHeader (headerCount + 1))
            |> processRead
          else
            machine.setFailure .badMessage
        else
          processHeaders machine
          |> processRead
      else
        machine

  | .readBody bodyState =>
      if shouldIgnoreBodyPull machine then
        let (machine, _pulledChunk, shouldContinue) := parseBody machine bodyState
        if shouldContinue then
          processRead machine
        else
          machine
      else
        machine

  | Reader.State.«continue» _ =>
      machine

  | .complete =>
      if (machine.reader.noMoreInput ∧ machine.reader.input.atEnd) ∨ ¬machine.keepAlive then
        machine.setReaderState .closed
      else
        machine

  | .closed =>
      machine

  | .failed error =>
      handleReaderFailed machine error

/--
Execute one step of the state machine.
-/
def step (machine : Machine dir) : Machine dir × StepResult dir :=
  let machine := machine.processRead.processWrite
  let (machine, events) := machine.takeEvents
  let (machine, output) := machine.takeOutput
  (machine, { events, output })

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
  let stalled :=
    pulledChunk.isNone &&
    !shouldIgnoreBodyPull machine &&
    match machine.reader.state with
    | .readBody _ => true
    | _ => false
  ({ machine with pullBodyStalled := stalled }, pulledChunk)

end Std.Http.Protocol.H1.Machine
