/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Init.Data.ByteArray

public section

namespace Std
namespace Http
namespace Util

/-
A structure that holds a bunch of ByteArrays and tracks the total size.
-/
structure BufferBuilder where
  data : Array ByteArray
  size : Nat
deriving Inhabited

namespace BufferBuilder

/--
An empty byte builder.
-/
@[inline]
def empty : BufferBuilder :=
  { data := #[], size := 0 }

/--
Append a single ByteArray to the byte builder.
-/
@[inline]
def push (c : BufferBuilder) (b : ByteArray) : BufferBuilder :=
  { data := c.data.push b, size := c.size + b.size }

/--
Append many ByteArrays at once.
-/
@[inline]
def append (c : BufferBuilder) (d : BufferBuilder) : BufferBuilder :=
  { data := c.data ++ d.data, size := c.size + d.size }

/--
Turn the combined structure into a single contiguous ByteArray.
-/
@[inline]
def toByteArray (c : BufferBuilder) : ByteArray :=
  if h : 1 = c.data.size then
    c.data[0]'(Nat.lt_of_le_of_lt (Nat.le_refl 0) ( Nat.le_of_eq h))
  else
    c.data.foldl (· ++ ·) (.emptyWithCapacity c.size)

/--
Build from a ByteArray directly.
-/
@[inline]
def ofByteArray (bs : ByteArray) : BufferBuilder :=
  { data := #[bs], size := bs.size }

/--
Build from an array of ByteArrays directly.
-/
@[inline]
def fromArray (bs : Array ByteArray) : BufferBuilder :=
  { data := bs, size := bs.foldl (· + ·.size) 0 }

/--
Check if it's an empty array.
-/
@[inline]
def isEmpty (bb : BufferBuilder) : Bool :=
  bb.size = 0

instance : HAppend BufferBuilder BufferBuilder BufferBuilder where
  hAppend := append

instance : Coe ByteArray BufferBuilder where
  coe := ofByteArray

instance : Coe (Array ByteArray) BufferBuilder where
  coe := fromArray

end BufferBuilder
end Util
end Http
end Std
