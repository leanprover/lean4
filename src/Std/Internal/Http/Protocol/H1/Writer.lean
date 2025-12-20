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

namespace Std.Http.Protocol.H1

open Internal

inductive Writer.State
  /--
  It only starts to write when part of the request is received.
  -/
  | pending

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
  | writingBody (mode : Body.Length)

  /--
  Shutting down, it will flush all the remaining data and cause it to shutdown.
  -/
  | shuttingDown

  /--
  State that it completed a single request and can go to the next one
  -/
  | complete

  /--
  State that it has completed and cannot process more data.
  -/
  | closed
deriving Inhabited, Repr, BEq

/--
Manages the writing state of the machine.
-/
structure Writer (dir : Direction) where
  /--
  This is all the data that the user is sending that is being accumulated.
  -/
  userData : Array Chunk := .empty

  /--
  All the data that is going to get out of the writer.
  -/
  outputData : ChunkedBuffer := .empty

  /--
  The state of the writer machine.
  -/
  state : Writer.State := .pending

  /--
  When the user specifies the exact size upfront, we can use Content-Length
  instead of chunked transfer encoding for streaming
  -/
  knownSize : Option Body.Length := none

  /--
  The outgoing message that will be written to the output
  -/
  messageHead : Message.Head dir.swap := {}

  /--
  The user sent the message
  -/
  sentMessage : Bool := false

  /--
  This flags that the writer is closed so if we start to write the body we know exactly the size.
  -/
  userClosedBody : Bool := false

namespace Writer

/--
Checks if the writer is closed (cannot process more data)
-/
@[inline]
def isReadyToSend {dir} (writer : Writer dir) : Bool :=
  match writer.state with
  | .closed | .complete => true
  | _ => writer.userClosedBody

/--
Checks if the writer is closed (cannot process more data)
-/
@[inline]
def isClosed (writer : Writer dir) : Bool :=
  match writer.state with
  | .closed => true
  | _ => false

/--
Checks if the writer has completed processing a request
-/
@[inline]
def isComplete (writer : Writer dir) : Bool :=
  match writer.state with
  | .complete => true
  | _ => false

/--
Checks if the writer can accept more data from the user
-/
@[inline]
def canAcceptData (writer : Writer dir) : Bool :=
  match writer.state with
  | .waitingHeaders => true
  | .waitingForFlush => true
  | .writingBody _ => !writer.userClosedBody
  | _ => false

/--
Marks the body as closed, indicating no more user data will be added
-/
@[inline]
def closeBody (writer : Writer dir) : Writer dir :=
  { writer with userClosedBody := true }

/--
Determines the transfer encoding mode based on explicit setting, body closure state, or defaults to chunked
-/
def determineTransferMode (writer : Writer dir) : Body.Length :=
  if let some mode := writer.knownSize then
    mode
  else if writer.userClosedBody then
    let size := writer.userData.foldl (fun x y => x + y.size) 0
    .fixed size
  else
    .chunked

/--
Adds user data chunks to the writer's buffer if the writer can accept data
-/
@[inline]
def addUserData (data : Array Chunk) (writer : Writer dir) : Writer dir :=
  if writer.canAcceptData then
    { writer with userData := writer.userData ++ data }
  else
    writer

/--
Writes accumulated user data to output using fixed-size encoding
-/
def writeFixedBody (writer : Writer dir) (limitSize : Nat) : Writer dir × Nat :=
  if writer.userData.size = 0 then
    (writer, limitSize)
  else
    let data := writer.userData.map Chunk.data
    let (chunks, totalSize) := data.foldl (fun (acc, size) ba =>
      if size >= limitSize then
        (acc, size)
      else
        let remaining := limitSize - size
        let takeSize := min ba.size remaining
        let chunk := ba.extract 0 takeSize
        (acc.push chunk, size + takeSize)
    ) (#[], 0)
    let outputData := writer.outputData.append (ChunkedBuffer.mk chunks totalSize)
    let remaining := limitSize - totalSize
    ({ writer with userData := #[], outputData }, remaining)

/--
Writes accumulated user data to output using chunked transfer encoding
-/
def writeChunkedBody (writer : Writer dir) : Writer dir :=
  if writer.userData.size = 0 then
    writer
  else
    let data := writer.userData
    { writer with userData := #[], outputData := data.foldl (Encode.encode .v11) writer.outputData }

/--
Writes the final chunk terminator (0\r\n\r\n) and transitions to complete state
-/
def writeFinalChunk (writer : Writer dir) : Writer dir :=
  let writer := writer.writeChunkedBody
  { writer with
    outputData := writer.outputData.append "0\r\n\r\n".toUTF8
    state := .complete
  }

/--
Extracts all accumulated output data and returns it with a cleared output buffer
-/
@[inline]
def takeOutput (writer : Writer dir) : Option (Writer dir × ByteArray) :=
  let output := writer.outputData.toByteArray
  some ({ writer with outputData := ChunkedBuffer.empty }, output)

/--
Updates the writer's state machine to a new state
-/
@[inline]
def setState (state : Writer.State) (writer : Writer dir) : Writer dir :=
  { writer with state }

/--
Writes the message headers to the output buffer
-/
private def writeHeaders (messageHead : Message.Head dir.swap) (writer : Writer dir) : Writer dir :=
  { writer with outputData := writer.outputData.push (toString messageHead).toUTF8 }

/--
Checks if the connection should be kept alive based on the Connection header
-/
def shouldKeepAlive (writer : Writer dir) : Bool :=
  writer.messageHead.headers.get? (.new "Connection")
  |>.map (fun v => v.value.toLower != "close")
  |>.getD true

/--
Closes the reader, transitioning to the closed state.
-/
@[inline]
def close (reader : Writer dir) : Writer dir :=
  { reader with state := .closed }

end Writer
