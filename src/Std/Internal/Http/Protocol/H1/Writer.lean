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
public import Std.Internal.Http.Protocol.H1.Error

public section

/-!
# HTTP/1.1 Writer

This module defines the writer state machine for generating outgoing HTTP/1.1 messages.
It handles encoding headers and body content for both fixed-length and chunked
transfer encodings.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Internal

/--
The state of the `Writer` state machine.
-/
inductive Writer.State
  /--
  Initial state before any outgoing message has been prepared.
  -/
  | pending

  /--
  Ready to write the message.
  -/
  | waitingHeaders

  /--
  This is the state that the machine waits for a condition to send the response header.
  -/
  | waitingForFlush

  /--
  Writing the headers.
  -/
  | writingHeaders

  /--
  Writing the body output (either fixed-length or chunked).
  -/
  | writingBody (mode : Body.Length)

  /--
  It will flush all the remaining data and cause it to shutdown the machine.
  -/
  | shuttingDown

  /--
  State that it completed a single request and can go to the next one.
  -/
  | complete

  /--
  State that it has completed and cannot process more data.
  -/
  | closed
deriving Inhabited, Repr, BEq

/--
Manages the writing state of the HTTP generating and writing machine.
-/
structure Writer (dir : Direction) where
  /--
  This is all the data that the user is sending that is being accumulated.
  -/
  userData : Array Chunk := .empty

  /--
  All the data that is produced by the writer.
  -/
  outputData : ChunkedBuffer := .empty

  /--
  The state of the writer machine.
  -/
  state : Writer.State := .pending

  /--
  When the user specifies the exact size upfront, we can use Content-Length
  instead of chunked transfer encoding for streaming.
  -/
  knownSize : Option Body.Length := none

  /--
  The outgoing message that will be written to the output.
  -/
  messageHead : Message.Head dir.swap := {}

  /--
  The user sent the message.
  -/
  sentMessage : Bool := false

  /--
  This flags that the body stream is closed so if we start to write the body we know exactly the size.
  -/
  userClosedBody : Bool := false

  /--
  When `true`, body bytes are intentionally omitted from the wire for this message
  (e.g. HEAD responses), while headers/framing metadata may still describe the
  hypothetical representation.
  -/
  omitBody : Bool := false

namespace Writer

/--
Checks if the writer is ready to send data to the output.
-/
@[inline]
def isReadyToSend {dir} (writer : Writer dir) : Bool :=
  match writer.state with
  | .closed | .complete => true
  | _ => writer.userClosedBody

/--
Checks if the writer is closed (cannot process more data).
-/
@[inline]
def isClosed (writer : Writer dir) : Bool :=
  match writer.state with
  | .closed => true
  | _ => false

/--
Checks if the writer has completed processing a request.
-/
@[inline]
def isComplete (writer : Writer dir) : Bool :=
  match writer.state with
  | .complete => true
  | _ => false

/--
Checks if the writer can accept more data from the user.
-/
@[inline]
def canAcceptData (writer : Writer dir) : Bool :=
  match writer.state with
  | .waitingHeaders => true
  | .waitingForFlush => true
  | .writingBody _ => !writer.userClosedBody
  | _ => false

/--
Marks the body as closed, indicating no more user data will be added.
-/
@[inline]
def closeBody (writer : Writer dir) : Writer dir :=
  { writer with userClosedBody := true }

/--
Determines the transfer encoding mode based on explicit setting, body closure state, or defaults to chunked.
-/
def determineTransferMode (writer : Writer dir) : Body.Length :=
  if let some mode := writer.knownSize then
    mode
  else if writer.userClosedBody then
    let size := writer.userData.foldl (fun x y => x + y.data.size) 0
    .fixed size
  else
    .chunked

/--
Adds user data chunks to the writer's buffer if the writer can accept data.
-/
@[inline]
def addUserData (data : Array Chunk) (writer : Writer dir) : Writer dir :=
  if writer.canAcceptData then
    { writer with userData := writer.userData ++ data }
  else
    writer

/--
Writes accumulated user data to output using fixed-size encoding.
-/
def writeFixedBody (writer : Writer dir) (limitSize : Nat) : Writer dir × Nat :=
  if writer.userData.size = 0 then
    (writer, limitSize)
  else
    let (chunks, pending, totalSize) := writer.userData.foldl (fun (state : Array ByteArray × Array Chunk × Nat) chunk =>
      let (acc, pending, size) := state
      if size >= limitSize then
        (acc, pending.push chunk, size)
      else
        let remaining := limitSize - size
        let takeSize := min chunk.data.size remaining
        let dataPart := chunk.data.extract 0 takeSize
        let acc := if takeSize = 0 then acc else acc.push dataPart
        let size := size + takeSize
        if takeSize < chunk.data.size then
          let pendingChunk : Chunk := { chunk with data := chunk.data.extract takeSize chunk.data.size }
          (acc, pending.push pendingChunk, size)
        else
          (acc, pending, size)
    ) (#[], #[], 0)
    let outputData := writer.outputData.append (ChunkedBuffer.ofArray chunks)
    let remaining := limitSize - totalSize
    ({ writer with userData := pending, outputData }, remaining)

/--
Writes accumulated user data to output using chunked transfer encoding.
-/
def writeChunkedBody (writer : Writer dir) : Writer dir :=
  if writer.userData.size = 0 then
    writer
  else
    let data := writer.userData
    { writer with userData := #[], outputData := data.foldl (Encode.encode .v11) writer.outputData }

/--
Writes the final chunk terminator (0\r\n\r\n) and transitions to complete state.
-/
def writeFinalChunk (writer : Writer dir) : Writer dir :=
  let writer := writer.writeChunkedBody
  { writer with
    outputData := writer.outputData.write "0\r\n\r\n".toUTF8
    state := .complete
  }

/--
Extracts all accumulated output data and returns it with a cleared output buffer.
-/
@[inline]
def takeOutput (writer : Writer dir) : Option (Writer dir × ByteArray) :=
  let output := writer.outputData.toByteArray
  some ({ writer with outputData := ChunkedBuffer.empty }, output)

/--
Updates the writer's state machine to a new state.
-/
@[inline]
def setState (state : Writer.State) (writer : Writer dir) : Writer dir :=
  { writer with state }

/--
Writes the message headers to the output buffer.
-/
private def writeHeaders (messageHead : Message.Head dir.swap) (writer : Writer dir) : Writer dir :=
  { writer with outputData := Internal.Encode.encode (v := .v11) writer.outputData messageHead }

/--
Checks if the connection should be kept alive based on the Connection header.
-/
def shouldKeepAlive (writer : Writer dir) : Bool :=
  writer.messageHead.headers.get? .connection
  |>.map (fun v => v.value.toLower != "close")
  |>.getD true

/--
Closes the writer, transitioning to the closed state.
-/
@[inline]
def close (writer : Writer dir) : Writer dir :=
  { writer with state := .closed }

end Writer
