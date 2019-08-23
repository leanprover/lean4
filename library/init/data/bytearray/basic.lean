/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.array.basic init.data.uint init.data.option.basic
universes u

structure ByteArray :=
(data : Array UInt8)

attribute [extern "lean_byte_array_mk"] ByteArray.mk
attribute [extern "lean_byte_array_data"] ByteArray.data

namespace ByteArray
@[extern c inline "lean_mk_empty_byte_array(#1)"]
def mkEmpty (c : @& Nat) : ByteArray :=
{ data := Array.empty }

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
def get : (@& ByteArray) → (@& Nat) → UInt8
| ⟨bs⟩, i => bs.get i

@[extern "lean_byte_array_set"]
def set : ByteArray → (@& Nat) → UInt8 → ByteArray
| ⟨bs⟩, i, b => ⟨bs.set i b⟩

def isEmpty (s : ByteArray) : Bool :=
s.size == 0

partial def toListAux (bs : ByteArray) : Nat → List UInt8 → List UInt8
| i, r =>
  if i < bs.size then
    toListAux (i+1) (bs.get i :: r)
  else
    r.reverse

def toList (bs : ByteArray) : List UInt8 :=
toListAux bs 0 []

end ByteArray

def List.toByteArrayAux : List UInt8 → ByteArray → ByteArray
| [],    r => r
| b::bs, r => List.toByteArrayAux bs (r.push b)

def List.toByteArray (bs : List UInt8) : ByteArray :=
bs.toByteArrayAux ByteArray.empty

instance : HasToString ByteArray :=
⟨fun bs => bs.toList.toString⟩
