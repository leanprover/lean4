/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.ToString
import Init.Data.Array.Lemmas
public import Init.Data.String.Basic
public import Init.Data.ByteArray.Basic

public section

/-!
# ChunkedBuffer

This module provides an efficient way to concatenate multiple `ByteArray`s by deferring the actual
concatenation until necessary. This is particularly useful in HTTP response building and streaming
scenarios where data is accumulated incrementally.
-/

namespace Std.Http.Internal

set_option linter.all true

/--
A structure that accumulates multiple `ByteArray`s efficiently by tracking them in an array and
maintaining the total size. This allows building large buffers without repeated allocations and copies.
-/
structure ChunkedBuffer where
  /--
  The accumulated byte arrays.
  -/
  data : Array ByteArray

  /--
  The total size in bytes of all accumulated arrays
  -/
  size : Nat

namespace ChunkedBuffer

/--
An empty `ChunkedBuffer`.
-/
@[inline]
def empty : ChunkedBuffer :=
  { data := #[], size := 0 }

/--
Pieces are copied into the previous piece while both together stay within this many bytes, so that
small writes (heads, chunk framing, short bodies) end up in one contiguous `ByteArray`.
-/
def mergeLimit : Nat := 4096

/--
Append a single `ByteArray` to the `ChunkedBuffer`. Small pieces are copied into the last piece
instead of being kept separately.
-/
@[inline]
def push (c : ChunkedBuffer) (b : ByteArray) : ChunkedBuffer :=
  if b.size == 0 then
    c
  else if h : 0 < c.data.size then
    if (c.data[c.data.size - 1]'(Nat.sub_lt h Nat.one_pos)).size + b.size ≤ mergeLimit then
      { data := c.data.modify (c.data.size - 1) (· ++ b), size := c.size + b.size }
    else
      { data := c.data.push b, size := c.size + b.size }
  else
    { data := c.data.push b, size := c.size + b.size }

/--
Writes a `ByteArray` to the `ChunkedBuffer`.
-/
@[inline]
def write (buffer : ChunkedBuffer) (data : ByteArray) : ChunkedBuffer :=
  buffer.push data

/--
Writes a `ChunkedBuffer` to the `ChunkedBuffer`.
-/
@[inline]
def append (buffer : ChunkedBuffer) (data : ChunkedBuffer) : ChunkedBuffer :=
  data.data.foldl push buffer

/--
Writes a `Char` to the `ChunkedBuffer`. Only the low byte is written (`Char.toUInt8`),
so this is only correct for ASCII characters.
-/
@[inline]
def writeChar (buffer : ChunkedBuffer) (data : Char) : ChunkedBuffer :=
  if h : 0 < buffer.data.size then
    if (buffer.data[buffer.data.size - 1]'(Nat.sub_lt h Nat.one_pos)).size < mergeLimit then
      { data := buffer.data.modify (buffer.data.size - 1) (·.push data.toUInt8), size := buffer.size + 1 }
    else
      { data := buffer.data.push (ByteArray.mk #[data.toUInt8]), size := buffer.size + 1 }
  else
    { data := buffer.data.push (ByteArray.mk #[data.toUInt8]), size := buffer.size + 1 }

/--
Writes a `String` to the `ChunkedBuffer`.
-/
@[inline]
def writeString (buffer : ChunkedBuffer) (data : String) : ChunkedBuffer :=
  buffer.push data.toUTF8

/--
Turn the combined structure into a single contiguous ByteArray.
-/
@[inline]
def toByteArray (cb : ChunkedBuffer) : ByteArray :=
  if h : 1 = cb.data.size then
    cb.data[0]'(Nat.le_of_eq h)
  else
    cb.data.foldl (· ++ ·) (.emptyWithCapacity cb.size)

/--
Build from a ByteArray directly.
-/
@[inline]
def ofByteArray (bs : ByteArray) : ChunkedBuffer :=
  { data := #[bs], size := bs.size }

/--
Build from an array of ByteArrays directly.
-/
@[inline]
def ofArray (bs : Array ByteArray) : ChunkedBuffer :=
  { data := bs, size := bs.foldl (· + ·.size) 0 }

/--
Checks whether the buffer is empty.
-/
@[inline]
def isEmpty (bb : ChunkedBuffer) : Bool :=
  bb.size = 0

instance : Inhabited ChunkedBuffer := ⟨empty⟩

instance : EmptyCollection ChunkedBuffer where
  emptyCollection := empty

instance : Coe ByteArray ChunkedBuffer where
  coe := ofByteArray

instance : Coe (Array ByteArray) ChunkedBuffer where
  coe := ofArray

end Std.Http.Internal.ChunkedBuffer
