/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Float
import Init.Data.Option.Basic
universe u

structure FloatArray where
  data : Array Float

attribute [extern "lean_float_array_mk"] FloatArray.mk
attribute [extern "lean_float_array_data"] FloatArray.data

namespace FloatArray
@[extern "lean_mk_empty_float_array"]
def mkEmpty (c : @& Nat) : FloatArray :=
  { data := #[] }

def empty : FloatArray :=
  mkEmpty 0

instance : Inhabited FloatArray := ⟨empty⟩

@[extern "lean_float_array_push"]
def push : FloatArray → Float → FloatArray
  | ⟨ds⟩, b => ⟨ds.push b⟩

@[extern "lean_float_array_size"]
def size : (@& FloatArray) → Nat
  | ⟨ds⟩ => ds.size

@[extern "lean_float_array_fget"]
def get (ds : @& FloatArray) (i : @& Fin ds.size) : Float :=
  match ds, i with
  | ⟨ds⟩, i => ds.get i

@[extern "lean_float_array_get"]
def get! : (@& FloatArray) → (@& Nat) → Float
  | ⟨ds⟩, i => ds.get! i

def get? (ds : FloatArray) (i : Nat) : Option Float :=
  if h : i < ds.size then
    ds.get ⟨i, h⟩
  else
    none

@[extern "lean_float_array_fset"]
def set (ds : FloatArray) (i : @& Fin ds.size) (d : Float) : FloatArray :=
  match ds, i with
  | ⟨ds⟩, i=> ⟨ds.set i d⟩

@[extern "lean_float_array_set"]
def set! : FloatArray → (@& Nat) → Float → FloatArray
  | ⟨ds⟩, i, d => ⟨ds.set! i d⟩

def isEmpty (s : FloatArray) : Bool :=
  s.size == 0

partial def toList (ds : FloatArray) : List Float :=
  let rec loop (i r) :=
    if h : i < ds.size then
      loop (i+1) (ds.get ⟨i, h⟩ :: r)
    else
      r.reverse
  loop 0 []

end FloatArray

def List.toFloatArray (ds : List Float) : FloatArray :=
  let rec loop
    | [],    r => r
    | b::ds, r => loop ds (r.push b)
  loop ds FloatArray.empty


instance : ToString FloatArray := ⟨fun ds => ds.toList.toString⟩
