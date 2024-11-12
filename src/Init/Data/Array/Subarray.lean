/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic

universe u v w

structure Subarray (α : Type u)  where
  array : Array α
  start : Nat
  stop : Nat
  start_le_stop : start ≤ stop
  stop_le_array_size : stop ≤ array.size

@[deprecated Subarray.array (since := "2024-04-13")]
abbrev Subarray.as (s : Subarray α) : Array α := s.array

@[deprecated Subarray.start_le_stop (since := "2024-04-13")]
theorem Subarray.h₁ (s : Subarray α) : s.start ≤ s.stop := s.start_le_stop

@[deprecated Subarray.stop_le_array_size (since := "2024-04-13")]
theorem Subarray.h₂ (s : Subarray α) : s.stop ≤ s.array.size := s.stop_le_array_size

namespace Subarray

def size (s : Subarray α) : Nat :=
  s.stop - s.start

theorem size_le_array_size {s : Subarray α} : s.size ≤ s.array.size := by
  let {array, start, stop, start_le_stop, stop_le_array_size} := s
  simp [size]
  apply Nat.le_trans (Nat.sub_le stop start)
  assumption

def get (s : Subarray α) (i : Fin s.size) : α :=
  have : s.start + i.val < s.array.size := by
   apply Nat.lt_of_lt_of_le _ s.stop_le_array_size
   have := i.isLt
   simp [size] at this
   rw [Nat.add_comm]
   exact Nat.add_lt_of_lt_sub this
  s.array[s.start + i.val]

instance : GetElem (Subarray α) Nat α fun xs i => i < xs.size where
  getElem xs i h := xs.get ⟨i, h⟩

@[inline] def getD (s : Subarray α) (i : Nat) (v₀ : α) : α :=
  if h : i < s.size then s[i] else v₀

abbrev get! [Inhabited α] (s : Subarray α) (i : Nat) : α :=
  getD s i default

def popFront (s : Subarray α) : Subarray α :=
  if h : s.start < s.stop then
    { s with start := s.start + 1, start_le_stop := Nat.le_of_lt_succ (Nat.add_lt_add_right h 1) }
  else
    s

/--
The empty subarray.
-/
protected def empty : Subarray α where
  array := #[]
  start := 0
  stop := 0
  start_le_stop := Nat.le_refl 0
  stop_le_array_size := Nat.le_refl 0

instance : EmptyCollection (Subarray α) :=
  ⟨Subarray.empty⟩

instance : Inhabited (Subarray α) :=
  ⟨{}⟩

@[inline] unsafe def forInUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (s : Subarray α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  let sz := USize.ofNat s.stop
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := s.array.uget i lcProof
      match (← f a b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop (USize.ofNat s.start) b

-- TODO: provide reference implementation
@[implemented_by Subarray.forInUnsafe]
protected opaque forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (s : Subarray α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
  pure b

instance : ForIn m (Subarray α) α where
  forIn := Subarray.forIn

@[inline]
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Subarray α) : m β :=
  as.array.foldlM f (init := init) (start := as.start) (stop := as.stop)

@[inline]
def foldrM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Subarray α) : m β :=
  as.array.foldrM f (init := init) (start := as.stop) (stop := as.start)

@[inline]
def anyM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Subarray α) : m Bool :=
  as.array.anyM p (start := as.start) (stop := as.stop)

@[inline]
def allM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Subarray α) : m Bool :=
  as.array.allM p (start := as.start) (stop := as.stop)

@[inline]
def forM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Subarray α) : m PUnit :=
  as.array.forM f (start := as.start) (stop := as.stop)

@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Subarray α) : m PUnit :=
  as.array.forRevM f (start := as.stop) (stop := as.start)

@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β) (as : Subarray α) : β :=
  Id.run <| as.foldlM f (init := init)

@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) (as : Subarray α) : β :=
  Id.run <| as.foldrM f (init := init)

@[inline]
def any {α : Type u} (p : α → Bool) (as : Subarray α) : Bool :=
  Id.run <| as.anyM p

@[inline]
def all {α : Type u} (p : α → Bool) (as : Subarray α) : Bool :=
  Id.run <| as.allM p

@[inline]
def findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Subarray α) (f : α → m (Option β)) : m (Option β) :=
  let rec @[specialize] find : (i : Nat) → i ≤ as.size → m (Option β)
    | 0,   _ => pure none
    | i+1, h => do
      have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
      let r ← f as[i]
      match r with
      | some _ => pure r
      | none   =>
        have : i ≤ as.size := Nat.le_of_lt this
        find i this
  find as.size (Nat.le_refl _)

@[inline]
def findRevM? {α : Type} {m : Type → Type w} [Monad m] (as : Subarray α) (p : α → m Bool) : m (Option α) :=
  as.findSomeRevM? fun a => return if (← p a) then some a else none

@[inline]
def findRev? {α : Type} (as : Subarray α) (p : α → Bool) : Option α :=
  Id.run <| as.findRevM? p

end Subarray

namespace Array
variable {α : Type u}

def toSubarray (as : Array α) (start : Nat := 0) (stop : Nat := as.size) : Subarray α :=
  if h₂ : stop ≤ as.size then
    if h₁ : start ≤ stop then
      { array := as, start := start, stop := stop,
        start_le_stop := h₁, stop_le_array_size := h₂ }
    else
      { array := as, start := stop, stop := stop,
        start_le_stop := Nat.le_refl _, stop_le_array_size := h₂ }
  else
    if h₁ : start ≤ as.size then
      { array := as,
        start := start,
        stop := as.size,
        start_le_stop := h₁,
        stop_le_array_size := Nat.le_refl _ }
    else
      { array := as,
        start := as.size,
        stop := as.size,
        start_le_stop := Nat.le_refl _,
        stop_le_array_size := Nat.le_refl _ }

@[coe]
def ofSubarray (s : Subarray α) : Array α := Id.run do
  let mut as := mkEmpty (s.stop - s.start)
  for a in s do
    as := as.push a
  return as

instance : Coe (Subarray α) (Array α) := ⟨ofSubarray⟩

syntax:max term noWs "[" withoutPosition(term ":" term) "]" : term
syntax:max term noWs "[" withoutPosition(term ":") "]" : term
syntax:max term noWs "[" withoutPosition(":" term) "]" : term

macro_rules
  | `($a[$start : $stop]) => `(Array.toSubarray $a $start $stop)
  | `($a[ : $stop])       => `(Array.toSubarray $a 0 $stop)
  | `($a[$start : ])      => `(let a := $a; Array.toSubarray a $start a.size)

end Array

def Subarray.toArray (s : Subarray α) : Array α :=
  Array.ofSubarray s

instance : Append (Subarray α) where
  append x y :=
   let a := x.toArray ++ y.toArray
   a.toSubarray 0 a.size

instance [Repr α] : Repr (Subarray α) where
  reprPrec s  _ := repr s.toArray ++ ".toSubarray"

instance [ToString α] : ToString (Subarray α) where
  toString s := toString s.toArray
