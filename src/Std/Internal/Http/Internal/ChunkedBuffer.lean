/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.String
public import Init.Data.ByteArray

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
  The accumulated byte arrays
  -/
  data : Array ByteArray

  /--
  The total size in bytes of all accumulated arrays
  -/
  size : Nat
deriving Inhabited

namespace ChunkedBuffer

/--
An empty `ChunkedBuffer`.
-/
@[inline]
def empty : ChunkedBuffer :=
  { data := #[], size := 0 }

/--
Append a single `ByteArray` to the `ChunkedBuffer`.
-/
@[inline]
def push (c : ChunkedBuffer) (b : ByteArray) : ChunkedBuffer :=
  { data := c.data.push b, size := c.size + b.size }

/--
Writes a `ByteArray` to the `ChunkedBuffer`.
-/
@[inline]
def write (buffer : ChunkedBuffer) (data : ByteArray) : ChunkedBuffer :=
  buffer.push data

/--
Writes a `Char` to the `ChunkedBuffer`.
-/
@[inline]
def writeChar (buffer : ChunkedBuffer) (data : Char) : ChunkedBuffer :=
  buffer.push (ByteArray.mk #[data.toUInt8])

/--
Writes a `String` to the `ChunkedBuffer`.
-/
@[inline]
def writeString (buffer : ChunkedBuffer) (data : String) : ChunkedBuffer :=
  buffer.push data.toUTF8

/--
Append many ByteArrays at once.
-/
@[inline]
def append (c : ChunkedBuffer) (d : ChunkedBuffer) : ChunkedBuffer :=
  { data := c.data ++ d.data, size := c.size + d.size }

/--
Turn the combined structure into a single contiguous ByteArray.
-/
@[inline]
def toByteArray (c : ChunkedBuffer) : ByteArray :=
  if h : 1 = c.data.size then
    c.data[0]'(Nat.le_of_eq h)
  else
    c.data.foldl (· ++ ·) (.emptyWithCapacity c.size)

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
def fromArray (bs : Array ByteArray) : ChunkedBuffer :=
  { data := bs, size := bs.foldl (· + ·.size) 0 }

/--
Check if it's an empty array.
-/
@[inline]
def isEmpty (bb : ChunkedBuffer) : Bool :=
  bb.size = 0

instance : EmptyCollection ChunkedBuffer where
  emptyCollection := empty

instance : HAppend ChunkedBuffer ChunkedBuffer ChunkedBuffer where
  hAppend := append

instance : Coe ByteArray ChunkedBuffer where
  coe := ofByteArray

instance : Coe (Array ByteArray) ChunkedBuffer where
  coe := fromArray

instance : Append ChunkedBuffer where
  append := append

instance : Repr ChunkedBuffer where
  reprPrec bb _ := s!"ChunkedBuffer.fromArray {bb.data}"

end Std.Http.Internal.ChunkedBuffer
