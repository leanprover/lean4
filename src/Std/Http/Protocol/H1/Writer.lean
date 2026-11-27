/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data
public import Std.Http.Internal

public section

/-!
# HTTP/1.1 Writer

The outgoing side of the HTTP/1.1 machine: the phase of the message being written, what the caller
said about its body, the body data the caller handed over, and the bytes ready for the transport.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

open Std.Http.Internal

/--
How the body being written is delimited on the wire.
-/
inductive Writer.BodyState where
  /-- `Content-Length` framing with `remaining` bytes still owed. -/
  | fixed (remaining : Nat)
  /-- Chunked transfer coding. -/
  | chunked
  /-- Raw bytes until the connection closes (a response of unknown length to HTTP/1.0). -/
  | closeDelimited
deriving Inhabited, Repr, BEq

/--
The phase of the outgoing message.
-/
inductive Writer.State where
  /-- No message to write yet: a server before the request head. -/
  | pending
  /-- Waiting for the message head (`send`). -/
  | waitingHeaders
  /-- The head was accepted and is written once `shouldFlush` holds. -/
  | waitingForFlush
  /-- The head was written; the body is being written. -/
  | writingBody (body : Writer.BodyState)
  /-- The message was written. -/
  | complete
  /-- Nothing more is written. -/
  | closed
deriving Inhabited, Repr, BEq

/--
What the caller said about the length of the outgoing body.
-/
inductive Writer.Framing where
  /-- Nothing: the length follows from the head and the body. -/
  | unset
  /-- The body has length `length`. -/
  | known (length : Body.Length)
  /-- No body bytes are written (as for a `HEAD` response); the head advertises `length`. -/
  | omitted (length : Option Body.Length)
deriving Inhabited, Repr, BEq

/--
The outgoing side of the machine.
-/
structure Writer where
  /-- The phase of the outgoing message. -/
  state : Writer.State := .pending
  /-- What the caller said about the length of the body. -/
  framing : Writer.Framing := .unset
  /-- Body chunks handed over and not written yet. -/
  userData : Array Chunk := .empty
  /-- The bytes of `userData`. -/
  userDataBytes : Nat := 0
  /-- The caller handed over the whole body. -/
  userClosedBody : Bool := false
  /-- The bytes ready for the transport. -/
  outputData : ChunkedBuffer := .empty

namespace Writer

/--
The body length the caller set.
-/
@[inline] def knownSize (writer : Writer) : Option Body.Length :=
  match writer.framing with
  | .unset => none
  | .known length => some length
  | .omitted length => length

/--
Whether no body bytes are written for the current message.
-/
@[inline] def omitBody (writer : Writer) : Bool :=
  writer.framing matches .omitted _

/--
Whether the writer is past waiting for the outgoing message head: `send` accepted it, or the writer
closed. Interim (1xx) responses leave it `false`.
-/
@[inline] def sentMessage (writer : Writer) : Bool :=
  !(writer.state matches .pending | .waitingHeaders)

/--
Whether no more body data will be written: the caller closed the body, or the message is over.
-/
@[inline] def noMoreUserData (writer : Writer) : Bool :=
  writer.userClosedBody || writer.state matches .closed | .complete

/--
Moves `userData` to the output as chunks of the chunked coding, dropping empty ones (an empty chunk
would end the body).
-/
def writeChunkedBody (writer : Writer) : Writer :=
  let outputData := writer.userData.foldl (init := writer.outputData) fun out c =>
    if c.data.isEmpty then out else out.pushChunk c
  { writer with userData := #[], userDataBytes := 0, outputData }

/--
Moves `userData` to the output as raw bytes.
-/
def writeRawBody (writer : Writer) : Writer :=
  { writer with
    outputData := writer.userData.foldl (·.push ·.data) writer.outputData
    userData := #[], userDataBytes := 0 }

end Std.Http.Protocol.H1.Writer
