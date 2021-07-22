/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Array.Subarray
import Init.Data.UInt
import Init.Data.Option.Basic
universe u

structure ByteArray where
  data : Array UInt8

attribute [extern "lean_byte_array_mk"] ByteArray.mk
attribute [extern "lean_byte_array_data"] ByteArray.data

namespace ByteArray
@[extern "lean_mk_empty_byte_array"]
def mkEmpty (c : @& Nat) : ByteArray :=
  { data := #[] }

def empty : ByteArray := mkEmpty 0

instance : Inhabited ByteArray := ⟨empty⟩

@[extern "lean_byte_array_push"]
def push : ByteArray → UInt8 → ByteArray
  | ⟨bs⟩, b => ⟨bs.push b⟩

@[extern "lean_byte_array_size"]
def size : (@& ByteArray) → Nat
  | ⟨bs⟩ => bs.size

@[extern "lean_byte_array_get"]
def get! : (@& ByteArray) → (@& Nat) → UInt8
  | ⟨bs⟩, i => bs.get! i

@[extern "lean_byte_array_set"]
def set! : ByteArray → (@& Nat) → UInt8 → ByteArray
  | ⟨bs⟩, i, b => ⟨bs.set! i b⟩

def isEmpty (s : ByteArray) : Bool :=
  s.size == 0

/--
  Copy the slice at `[srcOff, srcOff + len)` in `src` to `[destOff, destOff + len)` in `dest`, growing `dest` if necessary.
  If `exact` is `false`, the capacity will be doubled when grown. -/
@[extern "lean_byte_array_copy_slice"]
def copySlice (src : @& ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  ⟨dest.data.extract 0 destOff ++ src.data.extract srcOff len ++ dest.data.extract (destOff + len) dest.data.size⟩

def extract (a : ByteArray) (b e : Nat) : ByteArray :=
  a.copySlice b empty 0 (e - b)

protected def append (a : ByteArray) (b : ByteArray) : ByteArray :=
  -- we assume that `append`s may be repeated, so use asymptotic growing; use `copySlice` directly to customize
  b.copySlice 0 a a.size b.size false

instance : Append ByteArray := ⟨ByteArray.append⟩

partial def toList (bs : ByteArray) : List UInt8 :=
  let rec loop (i : Nat) (r : List UInt8) :=
    if i < bs.size then
      loop (i+1) (bs.get! i :: r)
    else
      r.reverse
  loop 0 []

@[inline] partial def findIdx? (a : ByteArray) (p : UInt8 → Bool) (start := 0) : Option Nat :=
  let rec @[specialize] loop (i : Nat) :=
    if i < a.size then
      if p (a.get! i) then some i else loop (i+1)
    else
      none
  loop start

end ByteArray

def List.toByteArray (bs : List UInt8) : ByteArray :=
  let rec loop
    | [],    r => r
    | b::bs, r => loop bs (r.push b)
  loop bs ByteArray.empty

instance : ToString ByteArray := ⟨fun bs => bs.toList.toString⟩

/-- Interpret a `ByteArray` of size 8 as a little-endian `UInt64`. -/
def ByteArray.toUInt64LE! (bs : ByteArray) : UInt64 :=
  assert! bs.size == 8
  (bs.get! 0).toUInt64 <<< 0x38 |||
  (bs.get! 1).toUInt64 <<< 0x30 |||
  (bs.get! 2).toUInt64 <<< 0x28 |||
  (bs.get! 3).toUInt64 <<< 0x20 |||
  (bs.get! 4).toUInt64 <<< 0x18 |||
  (bs.get! 5).toUInt64 <<< 0x10 |||
  (bs.get! 6).toUInt64 <<< 0x8  |||
  (bs.get! 7).toUInt64

/-- Interpret a `ByteArray` of size 8 as a big-endian `UInt64`. -/
def ByteArray.toUInt64BE! (bs : ByteArray) : UInt64 :=
  assert! bs.size == 8
  (bs.get! 7).toUInt64 <<< 0x38 |||
  (bs.get! 6).toUInt64 <<< 0x30 |||
  (bs.get! 5).toUInt64 <<< 0x28 |||
  (bs.get! 4).toUInt64 <<< 0x20 |||
  (bs.get! 3).toUInt64 <<< 0x18 |||
  (bs.get! 2).toUInt64 <<< 0x10 |||
  (bs.get! 1).toUInt64 <<< 0x8  |||
  (bs.get! 0).toUInt64
