/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time
public import Std.Http.Data
public import Std.Http.Internal
public import Std.Http.Protocol.H1.Parser
public import Std.Http.Protocol.H1.Config
public import Std.Http.Protocol.H1.Message
public import Std.Http.Protocol.H1.Error

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
  Waiting for the application to provide the outgoing message head via `send`.
  -/
  | waitingHeaders

  /--
  The message head has been provided; waiting for `shouldFlush` to become true before
  serializing headers to output.
  -/
  | waitingForFlush

  /--
  Writing a fixed-length body; `n` is the number of bytes still to be sent.
  -/
  | writingBodyFixed (n : Nat)

  /--
  Writing a chunked transfer-encoding body (HTTP/1.1).
  -/
  | writingBodyChunked

  /--
  Writing a connection-close body (HTTP/1.0 server, unknown length).
  Raw bytes are written without chunk framing; the peer reads until the connection closes.
  -/
  | writingBodyClosingFrame

  /--
  Completed writing a single message and ready to begin the next one.
  -/
  | complete

  /--
  Closed; no further data can be written.
  -/
  | closed
deriving Inhabited, Repr, BEq

/--
Manages the writing state of the HTTP generating and writing machine.
-/
structure Writer (dir : Direction) where
  /--
  Body chunks supplied by the user, accumulated before being flushed to output.
  -/
  userData : Array Chunk := .empty

  /--
  All the data produced by the writer, ready to be sent to the socket.
  -/
  outputData : ChunkedBuffer := .empty

  /--
  The state of the writer machine.
  -/
  state : Writer.State := match dir with | .receiving => .pending | .sending => .waitingHeaders

  /--
  When the user specifies the exact body size upfront, `Content-Length` framing is
  used instead of chunked transfer encoding.
  -/
  knownSize : Option Body.Length := none

  /--
  The outgoing message that will be written to the output.
  -/
  messageHead : Message.Head dir.swap := {}

  /--
  Whether the user has called `send` to provide the outgoing message head.
  -/
  sentMessage : Bool := false

  /--
  Set when the user has finished sending body data, allowing fixed-size framing
  to be determined upfront.
  -/
  userClosedBody : Bool := false

  /--
  When `true`, body bytes are intentionally omitted from the wire for this message
  (e.g. HEAD responses), while headers/framing metadata may still describe the
  hypothetical representation.
  -/
  omitBody : Bool := false

  /--
  Running total of bytes across all `userData` chunks, maintained incrementally
  to avoid an O(n) fold on every fixed-length write step.
  -/
  userDataBytes : Nat := 0

namespace Writer

/--
Returns `true` when no more user body data will arrive: either the user called
`closeBody`, or the writer has already transitioned to `complete` or `closed`.

Note: this does **not** mean the wire is ready to accept new bytes — a `closed`
writer cannot send anything. Use this to decide whether to flush pending body
data rather than to check writability.
-/
@[inline]
def noMoreUserData {dir} (writer : Writer dir) : Bool :=
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
  | .writingBodyFixed _
  | .writingBodyChunked
  | .writingBodyClosingFrame => !writer.userClosedBody
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
    .fixed writer.userDataBytes
  else
    .chunked

/--
Adds user data chunks to the writer's buffer if the writer can accept data.

Empty chunks (zero bytes of data) are accepted here but will be silently dropped
during the chunked-encoding write step — see `writeChunkedBody`.
-/
@[inline]
def addUserData (data : Array Chunk) (writer : Writer dir) : Writer dir :=
  if writer.canAcceptData then
    let extraBytes := data.foldl (fun acc c => acc + c.data.size) 0
    { writer with userData := writer.userData ++ data, userDataBytes := writer.userDataBytes + extraBytes }
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
    ({ writer with userData := pending, outputData, userDataBytes := writer.userDataBytes - totalSize }, remaining)

/--
Writes accumulated user data to output using chunked transfer encoding.

Empty chunks are silently discarded. See `Chunk.empty` for the protocol-level rationale.
-/
def writeChunkedBody (writer : Writer dir) : Writer dir :=
  if writer.userData.size = 0 then
    writer
  else
    let data := writer.userData.filter (fun c => !c.data.isEmpty)
    { writer with userData := #[], userDataBytes := 0, outputData := data.foldl (Encode.encode .v11) writer.outputData }

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
Writes accumulated user data to output as raw bytes (HTTP/1.0 connection-close framing).
No chunk framing is added; the peer reads until the connection closes.
-/
def writeRawBody (writer : Writer dir) : Writer dir :=
  { writer with
    outputData := writer.userData.foldl (fun buf c => buf.write c.data) writer.outputData,
    userData := #[], userDataBytes := 0 }

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
