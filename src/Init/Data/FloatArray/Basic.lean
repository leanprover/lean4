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

instance : Inhabited FloatArray where
  default := empty

instance : EmptyCollection FloatArray where
  emptyCollection := FloatArray.empty

@[extern "lean_float_array_push"]
def push : FloatArray → Float → FloatArray
  | ⟨ds⟩, b => ⟨ds.push b⟩

@[extern "lean_float_array_size"]
def size : (@& FloatArray) → Nat
  | ⟨ds⟩ => ds.size

@[extern "lean_sarray_size", simp]
def usize (a : @& FloatArray) : USize :=
  a.size.toUSize

@[extern "lean_float_array_uget"]
def uget : (a : @& FloatArray) → (i : USize) → i.toNat < a.size → Float
  | ⟨ds⟩, i, h => ds[i]

@[extern "lean_float_array_fget"]
def get : (ds : @& FloatArray) → (i : @& Nat) → (h : i < ds.size := by get_elem_tactic) → Float
  | ⟨ds⟩, i, h => ds.get i h

@[extern "lean_float_array_get"]
def get! : (@& FloatArray) → (@& Nat) → Float
  | ⟨ds⟩, i => ds.get! i

def get? (ds : FloatArray) (i : Nat) : Option Float :=
  if h : i < ds.size then
    some (ds.get i h)
  else
    none

instance : GetElem FloatArray Nat Float fun xs i => i < xs.size where
  getElem xs i h := xs.get i h

instance : GetElem FloatArray USize Float fun xs i => i.val < xs.size where
  getElem xs i h := xs.uget i h

@[extern "lean_float_array_uset"]
def uset : (a : FloatArray) → (i : USize) → Float → (h : i.toNat < a.size := by get_elem_tactic) → FloatArray
  | ⟨ds⟩, i, v, h => ⟨ds.uset i v h⟩

@[extern "lean_float_array_fset"]
def set : (ds : FloatArray) → (i : @& Nat) → Float → (h : i < ds.size := by get_elem_tactic) → FloatArray
  | ⟨ds⟩, i, d, h => ⟨ds.set i d h⟩

@[extern "lean_float_array_set"]
def set! : FloatArray → (@& Nat) → Float → FloatArray
  | ⟨ds⟩, i, d => ⟨ds.set! i d⟩

def isEmpty (s : FloatArray) : Bool :=
  s.size == 0

partial def toList (ds : FloatArray) : List Float :=
  let rec loop (i r) :=
    if h : i < ds.size then
      loop (i+1) (ds[i] :: r)
    else
      r.reverse
  loop 0 []

/--
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.
  This is similar to the `Array` version.
-/
-- TODO: avoid code duplication in the future after we improve the compiler.
@[inline] unsafe def forInUnsafe {β : Type v} {m : Type v → Type w} [Monad m] (as : FloatArray) (b : β) (f : Float → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

/-- Reference implementation for `forIn` -/
@[implemented_by FloatArray.forInUnsafe]
protected def forIn {β : Type v} {m : Type v → Type w} [Monad m] (as : FloatArray) (b : β) (f : Float → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance : ForIn m FloatArray Float where
  forIn := FloatArray.forIn

/-- See comment at `forInUnsafe` -/
-- TODO: avoid code duplication.
@[inline]
unsafe def foldlMUnsafe {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float → m β) (init : β) (as : FloatArray) (start := 0) (stop := as.size) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i+1) stop (← f b (as.uget i lcProof))
  if start < stop then
    if stop ≤ as.size then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else
    pure init

/-- Reference implementation for `foldlM` -/
@[implemented_by foldlMUnsafe]
def foldlM {β : Type v} {m : Type v → Type w} [Monad m] (f : β → Float → m β) (init : β) (as : FloatArray) (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          loop i' (j+1) (← f b (as[j]'(Nat.lt_of_lt_of_le hlt h)))
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

@[inline]
def foldl {β : Type v} (f : β → Float → β) (init : β) (as : FloatArray) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM f init start stop

end FloatArray

def List.toFloatArray (ds : List Float) : FloatArray :=
  let rec loop
    | [],    r => r
    | b::ds, r => loop ds (r.push b)
  loop ds FloatArray.empty


instance : ToString FloatArray := ⟨fun ds => ds.toList.toString⟩
