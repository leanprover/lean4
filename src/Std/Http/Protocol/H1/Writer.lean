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
  /--
  A server waiting for a request before it answers.
  -/
  | pending

  /--
  Waiting for the head of the message to send (`Machine.send`).
  -/
  | waitingHeaders

  /--
  The head was given; it is written once the body's framing is known (`Machine.shouldFlush`).
  -/
  | waitingForFlush

  /--
  Writing a body of known length, `n` bytes of which are left.
  -/
  | writingBodyFixed (n : Nat)

  /--
  Writing a body of unknown length: chunked, or else one that ends when the connection closes (an
  HTTP/1.0 response).
  -/
  | writingBodyOpen (chunked : Bool)

  /--
  The message was written.
  -/
  | complete

  /--
  No more messages will be written.
  -/
  | closed
deriving Inhabited, Repr, BEq

/--
The side of the machine that writes outgoing messages.
-/
structure Writer (dir : Direction) where
  /--
  Body chunks given by the caller and not written yet.
  -/
  userData : Array Chunk := .empty

  /--
  The bytes written, not yet taken by the caller (`Machine.step`).
  -/
  outputData : ChunkedBuffer := .empty

  /--
  Where the writer is.
  -/
  state : Writer.State := match dir with | .receiving => .pending | .sending => .waitingHeaders

  /--
  The body length the caller set (`Machine.setKnownSize`), if any.
  -/
  knownSize : Option Body.Length := none

  /--
  The head of the message being written.
  -/
  messageHead : Message.Head dir.swap := {}

  /--
  Whether the caller gave all of the body.
  -/
  userClosedBody : Bool := false

  /--
  The total size of `userData`.
  -/
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
Writes the buffered body data: as chunks when `chunked`, dropping empty ones, since an empty chunk
ends a chunked body; otherwise as it is, for a body of stated length or one that ends when the
connection closes.
-/
def writeBody (chunked : Bool) (writer : Writer dir) : Writer dir :=
  let outputData :=
    if chunked then
      writer.userData.foldl (init := writer.outputData) fun buf c =>
        if c.data.isEmpty then buf else buf.pushChunk c
    else
      writer.userData.foldl (fun buf c => buf.push c.data) writer.outputData
  { writer with outputData, userData := #[], userDataBytes := 0 }

end Writer

end Std.Http.Protocol.H1
