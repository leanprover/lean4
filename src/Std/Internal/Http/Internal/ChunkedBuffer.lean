/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
import Init.Data.Array.Lemmas
public import Init.Data.String
public import Init.Data.ByteArray
public import Init.Data.Queue

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
  data : Queue ByteArray

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
  { data := .empty, size := 0 }

/--
Append a single `ByteArray` to the `ChunkedBuffer`.
-/
@[inline]
def push (c : ChunkedBuffer) (b : ByteArray) : ChunkedBuffer :=
  { data := c.data.enqueue b, size := c.size + b.size }

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
Turn the combined structure into a single contiguous ByteArray.
-/
@[inline]
def toByteArray (c : ChunkedBuffer) : ByteArray :=
  let c := c.data.toArray

  if h : 1 = c.size then
    c[0]'(Nat.le_of_eq h)
  else
    c.foldl (· ++ ·) (.emptyWithCapacity c.size)

/--
Build from a ByteArray directly.
-/
@[inline]
def ofByteArray (bs : ByteArray) : ChunkedBuffer :=
  { data := .empty |>.enqueue bs, size := bs.size }

/--
Build from an array of ByteArrays directly.
-/
@[inline]
def ofArray (bs : Array ByteArray) : ChunkedBuffer :=
  { data := .empty |>.enqueueAll bs.toList , size := bs.foldl (· + ·.size) 0 }

/--
Dequeue the first `ByteArray` from the `ChunkedBuffer`, returning it along with the remaining buffer.
Returns `none` if the buffer is empty.
-/
@[inline]
def dequeue? (c : ChunkedBuffer) : Option (ByteArray × ChunkedBuffer) :=
  match c.data.dequeue? with
  | some (b, rest) => some (b, { data := rest, size := c.size - b.size })
  | none => none

/--
Push a `ByteArray` to the front of the `ChunkedBuffer`, so it will be dequeued first.
-/
@[inline]
def pushFront (c : ChunkedBuffer) (b : ByteArray) : ChunkedBuffer :=
  { data := { c.data with dList := b :: c.data.dList }, size := c.size + b.size }

/--
Extract exactly `n` bytes from the front of the `ChunkedBuffer`. If the buffer contains fewer
than `n` bytes, returns all available bytes. Returns the extracted bytes and the remaining buffer.
-/
partial def take (c : ChunkedBuffer) (n : Nat) : ByteArray × ChunkedBuffer :=
  if n ≥ c.size then
    (c.toByteArray, empty)
  else if n == 0 then
    (.empty, c)
  else
    go (.emptyWithCapacity n) n c
where
  go (acc : ByteArray) (remaining : Nat) (buf : ChunkedBuffer) : ByteArray × ChunkedBuffer :=
    match buf.dequeue? with
    | none => (acc, buf)
    | some (chunk, rest) =>
      if chunk.size ≤ remaining then
        go (acc ++ chunk) (remaining - chunk.size) rest
      else
        let taken := chunk.extract 0 remaining
        let leftover := chunk.extract remaining chunk.size
        (acc ++ taken, rest.pushFront leftover)

/--
Check if it's an empty array.
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
