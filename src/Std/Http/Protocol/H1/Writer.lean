/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Protocol.H1.Basic

public section

/-!
# HTTP/1.1 writer state

The state of the side of the machine that writes outgoing messages, and the encoding of their
bodies. The transitions are in `Std.Http.Protocol.H1`.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std.Http.Internal

/--
Where the writer is in the current message.
-/
inductive Writer.State
  /-- A server waiting for a request before it answers. -/
  | pending
  /-- Waiting for the head of the message to send (`Machine.send`). -/
  | waitingHeaders
  /-- The head was given; it is written once the body's framing is known (`Machine.shouldFlush`). -/
  | waitingForFlush
  /-- Writing a body of known length, `n` bytes of which are left. -/
  | writingBodyFixed (n : Nat)
  /-- Writing a chunked body. -/
  | writingBodyChunked
  /-- Writing a body that ends when the connection closes (an HTTP/1.0 response of unknown length). -/
  | writingBodyClosingFrame
  /-- The message was written. -/
  | complete
  /-- No more messages will be written. -/
  | closed
deriving Inhabited, Repr, BEq

/--
The side of the machine that writes outgoing messages.
-/
structure Writer (dir : Direction) where
  /-- Body chunks given by the caller and not written yet. -/
  userData : Array Chunk := .empty
  /-- The bytes written, not yet taken by the caller (`Machine.step`). -/
  outputData : ChunkedBuffer := .empty
  /-- Where the writer is. -/
  state : Writer.State := match dir with | .receiving => .pending | .sending => .waitingHeaders
  /-- The body length the caller set (`Machine.setKnownSize`), if any. -/
  knownSize : Option Body.Length := none
  /-- The head of the message being written. -/
  messageHead : Message.Head dir.swap := {}
  /-- Whether the caller gave all of the body. -/
  userClosedBody : Bool := false
  /-- Whether the body is left off the wire (a response to `HEAD`, or a status without content). -/
  omitBody : Bool := false
  /-- The total size of `userData`. -/
  userDataBytes : Nat := 0

namespace Writer

/--
Whether the writer is past waiting for the head of the message to send: `Machine.send` took a final
head, or the writer closed. Interim (1xx) responses leave it `false`.
-/
@[inline]
def sentMessage (writer : Writer dir) : Bool :=
  !(writer.state matches .pending | .waitingHeaders)

/--
Whether no more body data will come: the caller closed the body, or the message is over.
-/
@[inline]
def noMoreUserData {dir} (writer : Writer dir) : Bool :=
  match writer.state with
  | .closed | .complete => true
  | _ => writer.userClosedBody

/--
Whether the writer is closed.
-/
@[inline]
def isClosed (writer : Writer dir) : Bool :=
  writer.state matches .closed

/--
The framing of the body: the length the caller set, else the length of a body given in full, else
chunked.
-/
def determineTransferMode (writer : Writer dir) : Body.Length :=
  if let some mode := writer.knownSize then
    mode
  else if writer.userClosedBody then
    .fixed writer.userDataBytes
  else
    .chunked

/--
Writes buffered body data as chunks. Empty chunks are dropped, since an empty chunk ends a chunked
body.
-/
def writeChunkedBody (writer : Writer dir) : Writer dir :=
  if writer.userData.size = 0 then
    writer
  else
    let data := writer.userData.filter (fun c => !c.data.isEmpty)
    { writer with userData := #[], userDataBytes := 0, outputData := data.foldl ChunkedBuffer.pushChunk writer.outputData }

/--
Writes buffered body data and the last chunk, and completes the message.
-/
def writeFinalChunk (writer : Writer dir) : Writer dir :=
  let writer := writer.writeChunkedBody
  { writer with
    outputData := writer.outputData.push "0\r\n\r\n".toUTF8
    state := .complete
  }

/--
Writes buffered body data as it is: for a body of stated length, or one that ends when the connection
closes.
-/
def writeRawBody (writer : Writer dir) : Writer dir :=
  { writer with
    outputData := writer.userData.foldl (fun buf c => buf.push c.data) writer.outputData,
    userData := #[], userDataBytes := 0 }

end Writer

end Std.Http.Protocol.H1
