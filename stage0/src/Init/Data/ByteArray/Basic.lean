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
universes u

structure ByteArray :=
(data : Array UInt8)

attribute [extern "lean_byte_array_mk"] ByteArray.mk
attribute [extern "lean_byte_array_data"] ByteArray.data

namespace ByteArray
@[extern "lean_mk_empty_byte_array"]
def mkEmpty (c : @& Nat) : ByteArray :=
{ data := #[] }

def empty : ByteArray :=
mkEmpty 0

instance : Inhabited ByteArray :=
⟨empty⟩

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

instance : HasAppend ByteArray := ⟨ByteArray.append⟩

partial def toListAux (bs : ByteArray) : Nat → List UInt8 → List UInt8
| i, r =>
  if i < bs.size then
    toListAux (i+1) (bs.get! i :: r)
  else
    r.reverse

def toList (bs : ByteArray) : List UInt8 :=
toListAux bs 0 []

@[specialize] partial def findIdxAux (a : ByteArray) (p : UInt8 → Bool) : Nat → Option Nat
| i =>
  if i < a.size then
    if p (a.get! i) then some i else findIdxAux (i+1)
  else
    none

@[inline] def findIdx? (a : ByteArray) (p : UInt8 → Bool) : Option Nat :=
findIdxAux a p 0

end ByteArray

def List.toByteArrayAux : List UInt8 → ByteArray → ByteArray
| [],    r => r
| b::bs, r => List.toByteArrayAux bs (r.push b)

def List.toByteArray (bs : List UInt8) : ByteArray :=
bs.toByteArrayAux ByteArray.empty

instance : HasToString ByteArray :=
⟨fun bs => bs.toList.toString⟩
