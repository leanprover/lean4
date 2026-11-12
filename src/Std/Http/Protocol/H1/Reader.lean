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
# HTTP/1.1 reader state

The state of the side of the machine that reads incoming messages. The transitions are in
`Std.Http.Protocol.H1`.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
How the body being read is framed, and how far the reader is into it.
-/
inductive Reader.BodyState where
  /-- A body of known length, `remaining` bytes of which are left. -/
  | fixed (remaining : Nat)
  /-- Before a chunk-size line. -/
  | chunkedSize
  /-- Inside the data of a chunk, `remaining` bytes of which are left. -/
  | chunkedBody (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (remaining : Nat)
  /-- Inside the trailer section, after `count` fields. -/
  | trailers (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (count : Nat)
  /-- A body that ends when the connection closes. -/
  | closeDelimited
deriving Inhabited, Repr, BEq

/--
Where the reader is in the current message.
-/
inductive Reader.State (dir : Direction) : Type
  /-- Before a start line. -/
  | needStartLine : State dir
  /-- Inside the header section, after the given number of fields. -/
  | needHeader : Nat → State dir
  /-- Reading the body. -/
  | readBody : Reader.BodyState → State dir
  /-- Waiting for a `canContinue` decision before going on to the given state. -/
  | continue : State dir → State dir
  /-- A client waiting to send its request before it reads the response. -/
  | pending : State dir
  /-- The message was read; the exchange is not over yet. -/
  | complete
  /-- No more messages will be read: the connection ends, or the machine failed (`Machine.error`). -/
  | closed
deriving Inhabited, Repr, BEq

/--
The side of the machine that reads incoming messages.
-/
structure Reader (dir : Direction) where
  /-- Where the reader is. -/
  state : Reader.State dir := match dir with | .receiving => .needStartLine | .sending => .pending
  /-- The unread input. -/
  input : ByteArray.Iterator := ByteArray.emptyWithCapacity 4096 |>.iter
  /-- The head of the message being read. -/
  messageHead : Message.Head dir := {}
  /-- The number of messages already read on this connection. -/
  messageCount : Nat := 0
  /--
  The body bytes read for the current message. For a chunked body this includes the framing:
  chunk-size lines, the line break after each chunk's data, and the trailer section.
  -/
  bodyBytesRead : Nat := 0
  /-- The header bytes read for the current message, line breaks included. -/
  headerBytesRead : Nat := 0
  /-- Whether the peer closed its side of the connection, so no more input arrives. -/
  peerClosed : Bool := false
  /--
  Whether the machine stopped taking input, as after rejecting `Expect: 100-continue` or answering
  with an error. Input already buffered is still read.
  -/
  inputStopped : Bool := false
  /--
  Whether a head was read and its body has not ended. It stays set when the reader closes, so the
  machine still knows that the peer may be sending the rest of the message.
  -/
  inMessage : Bool := false
  /--
  How many unread bytes were already parsed without completing a line. The line is parsed again only
  once a line feed arrives after them, so a line that arrives in pieces is parsed once, not once per
  piece.
  -/
  tried : Nat := 0

namespace Reader

/--
Whether no more input will be fed: the peer closed its side, or the machine stopped taking input.
-/
@[inline]
def noMoreInput (reader : Reader dir) : Bool :=
  reader.peerClosed || reader.inputStopped

/--
Whether the reader is closed.
-/
@[inline]
def isClosed (reader : Reader dir) : Bool :=
  reader.state matches .closed

/--
Adds `data` to the unread input. If the input is exhausted, `data` replaces it. If none of it was
consumed, `data` is appended to it in place. Otherwise the unread bytes and `data` are copied into
one buffer of their combined size.
-/
@[inline]
def feed (data : ByteArray) (reader : Reader dir) : Reader dir :=
  let input := reader.input
  { reader with input :=
    if input.atEnd then
      data.iter
    else if input.pos = 0 then
      (input.array ++ data).iter
    else
      let rest := input.array.size - input.pos
      (input.array.copySlice input.pos (.emptyWithCapacity (rest + data.size)) 0 rest ++ data).iter }

/--
Replaces the unread input after an item was consumed.
-/
@[inline]
def setInput (input : ByteArray.Iterator) (reader : Reader dir) : Reader dir :=
  { reader with input, tried := 0 }

/--
Adds a header field to the head being read.
-/
@[inline]
def addHeader (name : Header.Name) (value : Header.Value) (reader : Reader dir) : Reader dir :=
  match dir with
  | .sending | .receiving =>
    { reader with messageHead := { reader.messageHead with headers := reader.messageHead.headers.insert name value } }

/--
Starts reading the next head on the same connection, keeping the unread input.
-/
@[inline]
def reset (reader : Reader dir) : Reader dir :=
  { reader with
    state := .needStartLine
    bodyBytesRead := 0
    headerBytesRead := 0
    messageHead := {} }

/--
Starts reading the final response after an interim (1xx) one. The interim head's bytes stay counted
toward `maxHeaderBytes`, so a run of 1xx responses is bounded.
-/
@[inline]
def resetAfterInterim (reader : Reader dir) : Reader dir :=
  { reader with
    state := .needStartLine
    bodyBytesRead := 0
    inMessage := false
    messageHead := {} }

/--
The number of unread input bytes.
-/
@[inline]
def remainingBytes (reader : Reader dir) : Nat :=
  reader.input.array.size - reader.input.pos

/--
Counts `n` more body bytes.
-/
@[inline]
def addBodyBytes (n : Nat) (reader : Reader dir) : Reader dir :=
  { reader with bodyBytesRead := reader.bodyBytesRead + n }

@[simp]
theorem remainingBytes_eq (reader : Reader dir) :
    reader.remainingBytes = reader.input.remainingBytes := by
  unfold remainingBytes; rfl

@[simp]
theorem input_setInput (input : ByteArray.Iterator) (reader : Reader dir) :
    (reader.setInput input).input = input := by
  unfold setInput; rfl

@[simp]
theorem input_addHeader (name : Header.Name) (value : Header.Value) (reader : Reader dir) :
    (reader.addHeader name value).input = reader.input := by
  unfold addHeader; cases dir <;> rfl

@[simp]
theorem input_addBodyBytes (n : Nat) (reader : Reader dir) :
    (reader.addBodyBytes n).input = reader.input := by
  unfold addBodyBytes; rfl

end Reader

end Std.Http.Protocol.H1
