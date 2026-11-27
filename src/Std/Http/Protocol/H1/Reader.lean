/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Http.Data
public import Std.Http.Protocol.H1.Config
public import Std.Http.Protocol.H1.Input

public section

/-!
# HTTP/1.1 Reader

The incoming side of the HTTP/1.1 machine: the phase of the message being read and the input.
-/

namespace Std.Http.Protocol.H1

set_option linter.all true

/--
How the body being read is delimited, and how far into it the reader is.
-/
inductive Reader.BodyState where
  /-- A `Content-Length` body with `remaining` bytes left. -/
  | fixed (remaining : Nat)
  /-- Before a chunk-size line. -/
  | chunkedSize
  /-- Inside the data of a chunk with extensions `ext`, `remaining` bytes left. -/
  | chunkedBody (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (remaining : Nat)
  /-- In the trailer section after the last chunk, `count` fields into it. -/
  | trailers (ext : Array (Chunk.ExtensionName × Option Chunk.ExtensionValue)) (count : Nat)
  /-- A body that ends when the peer closes the connection. -/
  | closeDelimited
deriving Inhabited, Repr, BEq

/--
The phase of the incoming message.
-/
inductive Reader.State where
  /-- No message is expected: a client with no request outstanding. -/
  | pending
  /-- Before a start line. -/
  | needStartLine
  /-- In the header section, `count` fields into it. -/
  | needHeader (count : Nat)
  /-- In the body. -/
  | readBody (body : Reader.BodyState)
  /-- A server waits for the `canContinue` decision on `Expect: 100-continue` before `body`. -/
  | «continue» (body : Reader.BodyState)
  /-- The message was read; the next one waits for the exchange to end. -/
  | complete
  /-- Nothing more is read. -/
  | closed
deriving Inhabited, Repr, BEq

/--
The incoming side of the machine.
-/
structure Reader where
  /-- The phase of the incoming message. -/
  state : Reader.State := .needStartLine
  /-- The input not read yet. -/
  input : ByteArray.Iterator := ByteArray.emptyWithCapacity 4096 |>.iter
  /-- The number of messages of earlier exchanges on this connection. -/
  messageCount : Nat := 0
  /--
  The body bytes read for the current message. For a chunked body this includes the framing:
  chunk-size lines, the line break after each chunk's data, and the trailer section.
  -/
  bodyBytesRead : Nat := 0
  /-- The header bytes of the current message: name, value and 4 bytes per field line. -/
  headerBytesRead : Nat := 0
  /-- The peer closed its side of the connection. -/
  peerClosed : Bool := false
  /-- The machine stopped taking input. Input already buffered is still parsed. -/
  inputStopped : Bool := false
  /-- The scan of the incomplete line at the start of `input`, resumed by the next read of it. -/
  lineScan : LineScan := {}

namespace Reader

/--
Whether no further input will be fed: the peer closed its side, or the machine stopped taking input.
-/
@[inline] def noMoreInput (reader : Reader) : Bool :=
  reader.peerClosed || reader.inputStopped

/--
The number of bytes not read yet.
-/
@[inline] def remainingBytes (reader : Reader) : Nat :=
  reader.input.array.size - reader.input.pos

/--
Appends `data` to the input (`Input.append`).
-/
@[inline] def feed (data : ByteArray) (reader : Reader) : Reader :=
  { reader with input := Input.append reader.input data }

end Std.Http.Protocol.H1.Reader
