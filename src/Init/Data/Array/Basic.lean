/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Fin.Basic
import Init.Data.UInt.BasicAux
import Init.Data.Repr
import Init.Data.ToString.Basic
import Init.GetElem
import Init.Data.List.ToArrayImpl
import Init.Data.Array.Set

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

universe u v w

/-! ### Array literal syntax -/

/-- Syntax for `Array α`. -/
syntax (name := «term#[_,]») "#[" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(#[ $elems,* ]) => `(List.toArray [ $elems,* ])

recommended_spelling "empty" for "#[]" in [«term#[_,]»]
recommended_spelling "singleton" for "#[x]" in [«term#[_,]»]

variable {α : Type u}

namespace Array

@[deprecated toList (since := "2024-10-13")] abbrev data := @toList

/-! ### Preliminary theorems -/

@[simp] theorem size_set (xs : Array α) (i : Nat) (v : α) (h : i < xs.size) :
    (set xs i v h).size = xs.size :=
  List.length_set ..

@[simp] theorem size_push (xs : Array α) (v : α) : (push xs v).size = xs.size + 1 :=
  List.length_concat ..

theorem ext (xs ys : Array α)
    (h₁ : xs.size = ys.size)
    (h₂ : (i : Nat) → (hi₁ : i < xs.size) → (hi₂ : i < ys.size) → xs[i] = ys[i])
    : xs = ys := by
  let rec extAux (as bs : List α)
      (h₁ : as.length = bs.length)
      (h₂ : (i : Nat) → (hi₁ : i < as.length) → (hi₂ : i < bs.length) → as[i] = bs[i])
      : as = bs := by
    induction as generalizing bs with
    | nil =>
      cases bs with
      | nil       => rfl
      | cons b bs => rw [List.length_cons] at h₁; injection h₁
    | cons a as ih =>
      cases bs with
      | nil => rw [List.length_cons] at h₁; injection h₁
      | cons b bs =>
        have hz₁ : 0 < (a::as).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have hz₂ : 0 < (b::bs).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have headEq : a = b := h₂ 0 hz₁ hz₂
        have h₁' : as.length = bs.length := by rw [List.length_cons, List.length_cons] at h₁; injection h₁
        have h₂' : (i : Nat) → (hi₁ : i < as.length) → (hi₂ : i < bs.length) → as[i] = bs[i] := by
          intro i hi₁ hi₂
          have hi₁' : i+1 < (a::as).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have hi₂' : i+1 < (b::bs).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have : (a::as)[i+1] = (b::bs)[i+1] := h₂ (i+1) hi₁' hi₂'
          apply this
        have tailEq : as = bs := ih bs h₁' h₂'
        rw [headEq, tailEq]
  cases xs; cases ys
  apply congrArg
  apply extAux
  assumption
  assumption

theorem ext' {xs ys : Array α} (h : xs.toList = ys.toList) : xs = ys := by
  cases xs; cases ys; simp at h; rw [h]

@[simp] theorem toArrayAux_eq (as : List α) (acc : Array α) : (as.toArrayAux acc).toList = acc.toList ++ as := by
  induction as generalizing acc <;> simp [*, List.toArrayAux, Array.push, List.append_assoc, List.concat_eq_append]

@[simp] theorem toArray_toList (xs : Array α) : xs.toList.toArray = xs := rfl

@[simp] theorem getElem_toList {xs : Array α} {i : Nat} (h : i < xs.size) : xs.toList[i] = xs[i] := rfl

@[simp] theorem getElem?_toList {xs : Array α} {i : Nat} : xs.toList[i]? = xs[i]? := by
  simp [getElem?_def]

/-- `a ∈ as` is a predicate which asserts that `a` is in the array `as`. -/
-- NB: This is defined as a structure rather than a plain def so that a lemma
-- like `sizeOf_lt_of_mem` will not apply with no actual arrays around.
structure Mem (as : Array α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (Array α) where
  mem := Mem

theorem mem_def {a : α} {as : Array α} : a ∈ as ↔ a ∈ as.toList :=
  ⟨fun | .mk h => h, Array.Mem.mk⟩

@[simp] theorem mem_toArray {a : α} {l : List α} : a ∈ l.toArray ↔ a ∈ l := by
  simp [mem_def]

@[simp] theorem getElem_mem {xs : Array α} {i : Nat} (h : i < xs.size) : xs[i] ∈ xs := by
  rw [Array.mem_def, ← getElem_toList]
  apply List.getElem_mem

end Array

namespace List

@[deprecated Array.toArray_toList (since := "2025-02-17")]
abbrev toArray_toList := @Array.toArray_toList

-- This does not need to be a simp lemma, as already after the `whnfR` the right hand side is `as`.
theorem toList_toArray (as : List α) : as.toArray.toList = as := rfl

@[deprecated toList_toArray (since := "2025-02-17")]
abbrev _root_.Array.toList_toArray := @List.toList_toArray

@[simp] theorem size_toArray (as : List α) : as.toArray.size = as.length := by simp [Array.size]

@[deprecated size_toArray (since := "2025-02-17")]
abbrev _root_.Array.size_toArray := @List.size_toArray

@[simp] theorem getElem_toArray {xs : List α} {i : Nat} (h : i < xs.toArray.size) :
    xs.toArray[i] = xs[i]'(by simpa using h) := rfl

@[simp] theorem getElem?_toArray {xs : List α} {i : Nat} : xs.toArray[i]? = xs[i]? := by
  simp [getElem?_def]

@[simp] theorem getElem!_toArray [Inhabited α] {xs : List α} {i : Nat} :
    xs.toArray[i]! = xs[i]! := by
  simp [getElem!_def]

end List

namespace Array

@[deprecated toList_toArray (since := "2024-09-09")] abbrev data_toArray := @List.toList_toArray

@[deprecated Array.toList (since := "2024-09-10")] abbrev Array.data := @Array.toList

/-! ### Externs -/

/-- Low-level version of `size` that directly queries the C array object cached size.
    While this is not provable, `usize` always returns the exact size of the array since
    the implementation only supports arrays of size less than `USize.size`.
-/
@[extern "lean_array_size", simp]
def usize (a : @& Array α) : USize := a.size.toUSize

/-- Low-level version of `fget` which is as fast as a C array read.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fget` may be slightly slower than `uget`. -/
@[extern "lean_array_uget", simp]
def uget (a : @& Array α) (i : USize) (h : i.toNat < a.size) : α :=
  a[i.toNat]

/-- Low-level version of `fset` which is as fast as a C array fset.
   `Fin` values are represented as tag pointers in the Lean runtime. Thus,
   `fset` may be slightly slower than `uset`. -/
@[extern "lean_array_uset"]
def uset (xs : Array α) (i : USize) (v : α) (h : i.toNat < xs.size) : Array α :=
  xs.set i.toNat v h

@[extern "lean_array_pop"]
def pop (xs : Array α) : Array α where
  toList := xs.toList.dropLast

@[simp] theorem size_pop (xs : Array α) : xs.pop.size = xs.size - 1 := by
  match xs with
  | ⟨[]⟩ => rfl
  | ⟨a::as⟩ => simp [pop, Nat.succ_sub_succ_eq_sub, size]

@[extern "lean_mk_array"]
def mkArray {α : Type u} (n : Nat) (v : α) : Array α where
  toList := List.replicate n v

/--
Swaps two entries in an array.

This will perform the update destructively provided that `a` has a reference
count of 1 when called.
-/
@[extern "lean_array_fswap"]
def swap (xs : Array α) (i j : @& Nat) (hi : i < xs.size := by get_elem_tactic) (hj : j < xs.size := by get_elem_tactic) : Array α :=
  let v₁ := xs[i]
  let v₂ := xs[j]
  let xs'  := xs.set i v₂
  xs'.set j v₁ (Nat.lt_of_lt_of_eq hj (size_set xs i v₂ _).symm)

@[simp] theorem size_swap (xs : Array α) (i j : Nat) {hi hj} : (xs.swap i j hi hj).size = xs.size := by
  show ((xs.set i xs[j]).set j xs[i]
    (Nat.lt_of_lt_of_eq hj (size_set xs i xs[j] _).symm)).size = xs.size
  rw [size_set, size_set]

/--
Swaps two entries in an array, or returns the array unchanged if either index is out of bounds.

This will perform the update destructively provided that `a` has a reference
count of 1 when called.
-/
@[extern "lean_array_swap"]
def swapIfInBounds (xs : Array α) (i j : @& Nat) : Array α :=
  if h₁ : i < xs.size then
  if h₂ : j < xs.size then swap xs i j
  else xs
  else xs

@[deprecated swapIfInBounds (since := "2024-11-24")] abbrev swap! := @swapIfInBounds

/-! ### GetElem instance for `USize`, backed by `uget` -/

instance : GetElem (Array α) USize α fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

/-! ### Definitions -/

instance : EmptyCollection (Array α) := ⟨Array.empty⟩
instance : Inhabited (Array α) where
  default := Array.empty

def isEmpty (xs : Array α) : Bool :=
  xs.size = 0

@[specialize]
def isEqvAux (xs ys : Array α) (hsz : xs.size = ys.size) (p : α → α → Bool) :
    ∀ (i : Nat) (_ : i ≤ xs.size), Bool
  | 0, _ => true
  | i+1, h =>
    p xs[i] (ys[i]'(hsz ▸ h)) && isEqvAux xs ys hsz p i (Nat.le_trans (Nat.le_add_right i 1) h)

@[inline] def isEqv (xs ys : Array α) (p : α → α → Bool) : Bool :=
  if h : xs.size = ys.size then
    isEqvAux xs ys h p xs.size (Nat.le_refl xs.size)
  else
    false

instance [BEq α] : BEq (Array α) :=
  ⟨fun xs ys => isEqv xs ys BEq.beq⟩

/--
`ofFn f` with `f : Fin n → α` returns the list whose ith element is `f i`.
```
ofFn f = #[f 0, f 1, ... , f(n - 1)]
``` -/
def ofFn {n} (f : Fin n → α) : Array α := go 0 (mkEmpty n) where
  /-- Auxiliary for `ofFn`. `ofFn.go f i acc = acc ++ #[f i, ..., f(n - 1)]` -/
  @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < n then go (i+1) (acc.push (f ⟨i, h⟩)) else acc
  decreasing_by simp_wf; decreasing_trivial_pre_omega

/-- The array `#[0, 1, ..., n - 1]`. -/
def range (n : Nat) : Array Nat :=
  ofFn fun (i : Fin n) => i

/-- The array `#[start, start + step, ..., start + step * (size - 1)]`. -/
def range' (start size : Nat) (step : Nat := 1) : Array Nat :=
  ofFn fun (i : Fin size) => start + step * i

@[inline] protected def singleton (v : α) : Array α := #[v]

/--
Return the last element of an array, or panic if the array is empty.

See `back` for the version that requires a proof the array is non-empty,
or `back?` for the version that returns an option.
-/
def back! [Inhabited α] (xs : Array α) : α :=
  xs[xs.size - 1]!

/--
Return the last element of an array, given a proof that the array is not empty.

See `back!` for the version that panics if the array is empty,
or `back?` for the version that returns an option.
-/
def back (xs : Array α) (h : 0 < xs.size := by get_elem_tactic) : α :=
  xs[xs.size - 1]'(Nat.sub_one_lt_of_lt h)

/--
Return the last element of an array, or `none` if the array is empty.

See `back!` for the version that panics if the array is empty,
or `back` for the version that requires a proof the array is non-empty.
-/
def back? (xs : Array α) : Option α :=
  xs[xs.size - 1]?

@[deprecated "Use `a[i]?` instead." (since := "2025-02-12")]
def get? (xs : Array α) (i : Nat) : Option α :=
  if h : i < xs.size then some xs[i] else none

@[inline] def swapAt (xs : Array α) (i : Nat) (v : α) (hi : i < xs.size := by get_elem_tactic) : α × Array α :=
  let e := xs[i]
  let xs' := xs.set i v
  (e, xs')

@[inline]
def swapAt! (xs : Array α) (i : Nat) (v : α) : α × Array α :=
  if h : i < xs.size then
    swapAt xs i v
  else
    have : Inhabited (α × Array α) := ⟨(v, xs)⟩
    panic! ("index " ++ toString i ++ " out of bounds")

/-- `shrink a n` returns the first `n` elements of `a`, implemented by repeatedly popping the last element. -/
def shrink (xs : Array α) (n : Nat) : Array α :=
  let rec loop
    | 0,   xs => xs
    | n+1, xs => loop n xs.pop
  loop (xs.size - n) xs

/-- `take a n` returns the first `n` elements of `a`, implemented by copying the first `n` elements. -/
abbrev take (xs : Array α) (i : Nat) : Array α := extract xs 0 i

@[simp] theorem take_eq_extract (xs : Array α) (i : Nat) : xs.take i = xs.extract 0 i := rfl

/-- `drop a n` removes the first `n` elements of `a`, implemented by copying the remaining elements. -/
abbrev drop (xs : Array α) (i : Nat) : Array α := extract xs i xs.size

@[simp] theorem drop_eq_extract (xs : Array α) (i : Nat) : xs.drop i = xs.extract i xs.size := rfl

@[inline]
unsafe def modifyMUnsafe [Monad m] (xs : Array α) (i : Nat) (f : α → m α) : m (Array α) := do
  if h : i < xs.size then
    let v                := xs[i]
    -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
    -- Note: we assume that arrays have a uniform representation irrespective
    -- of the element type, and that it is valid to store `box(0)` in any array.
    let xs'               := xs.set i (unsafeCast ())
    let v ← f v
    pure <| xs'.set i v (Nat.lt_of_lt_of_eq h (size_set xs ..).symm)
  else
    pure xs

@[implemented_by modifyMUnsafe]
def modifyM [Monad m] (xs : Array α) (i : Nat) (f : α → m α) : m (Array α) := do
  if h : i < xs.size then
    let v   := xs[i]
    let v ← f v
    pure <| xs.set i v
  else
    pure xs

@[inline]
def modify (xs : Array α) (i : Nat) (f : α → α) : Array α :=
  Id.run <| modifyM xs i f

set_option linter.indexVariables false in -- Changing `idx` causes bootstrapping issues, haven't investigated.
@[inline]
def modifyOp (xs : Array α) (idx : Nat) (f : α → α) : Array α :=
  xs.modify idx f

/--
  We claim this unsafe implementation is correct because an array cannot have more than `usizeSz` elements in our runtime.

  This kind of low level trick can be removed with a little bit of compiler support. For example, if the compiler simplifies `as.size < usizeSz` to true. -/
@[inline] unsafe def forIn'Unsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let sz := as.usize
  let rec @[specialize] loop (i : USize) (b : β) : m β := do
    if i < sz then
      let a := as.uget i lcProof
      match (← f a lcProof b) with
      | ForInStep.done  b => pure b
      | ForInStep.yield b => loop (i+1) b
    else
      pure b
  loop 0 b

/-- Reference implementation for `forIn'` -/
@[implemented_by Array.forIn'Unsafe]
protected def forIn' {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : Array α) (b : β) (f : (a : α) → a ∈ as → β → m (ForInStep β)) : m β :=
  let rec loop (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    match i, h with
    | 0,   _ => pure b
    | i+1, h =>
      have h' : i < as.size            := Nat.lt_of_lt_of_le (Nat.lt_succ_self i) h
      have : as.size - 1 < as.size     := Nat.sub_lt (Nat.zero_lt_of_lt h') (by decide)
      have : as.size - 1 - i < as.size := Nat.lt_of_le_of_lt (Nat.sub_le (as.size - 1) i) this
      match (← f as[as.size - 1 - i] (getElem_mem this) b) with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop i (Nat.le_of_lt h') b
  loop as.size (Nat.le_refl _) b

instance : ForIn' m (Array α) α inferInstance where
  forIn' := Array.forIn'

-- No separate `ForIn` instance is required because it can be derived from `ForIn'`.

-- We simplify `Array.forIn'` to `forIn'`.
@[simp] theorem forIn'_eq_forIn' [Monad m] : @Array.forIn' α β m _ = forIn' := rfl

/-- See comment at `forIn'Unsafe` -/
@[inline]
unsafe def foldlMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β :=
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
def foldlM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : β → α → m β) (init : β) (as : Array α) (start := 0) (stop := as.size) : m β :=
  let fold (stop : Nat) (h : stop ≤ as.size) :=
    let rec loop (i : Nat) (j : Nat) (b : β) : m β := do
      if hlt : j < stop then
        match i with
        | 0    => pure b
        | i'+1 =>
          have : j < as.size := Nat.lt_of_lt_of_le hlt h
          loop i' (j+1) (← f b as[j])
      else
        pure b
    loop (stop - start) start init
  if h : stop ≤ as.size then
    fold stop h
  else
    fold as.size (Nat.le_refl _)

/-- See comment at `forIn'Unsafe` -/
@[inline]
unsafe def foldrMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m β :=
  let rec @[specialize] fold (i : USize) (stop : USize) (b : β) : m β := do
    if i == stop then
      pure b
    else
      fold (i-1) stop (← f (as.uget (i-1) lcProof) b)
  if start ≤ as.size then
    if stop < start then
      fold (USize.ofNat start) (USize.ofNat stop) init
    else
      pure init
  else if stop < as.size then
    fold (USize.ofNat as.size) (USize.ofNat stop) init
  else
    pure init

/-- Reference implementation for `foldrM` -/
@[implemented_by foldrMUnsafe]
def foldrM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → β → m β) (init : β) (as : Array α) (start := as.size) (stop := 0) : m β :=
  let rec fold (i : Nat) (h : i ≤ as.size) (b : β) : m β := do
    if i == stop then
      pure b
    else match i, h with
      | 0, _   => pure b
      | i+1, h =>
        have : i < as.size := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) h
        fold i (Nat.le_of_lt this) (← f as[i] b)
  if h : start ≤ as.size then
    if stop < start then
      fold start h init
    else
      pure init
  else if stop < as.size then
    fold as.size (Nat.le_refl _) init
  else
    pure init

/-- See comment at `forIn'Unsafe` -/
@[inline]
unsafe def mapMUnsafe {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) (as : Array α) : m (Array β) :=
  let sz := as.usize
  let rec @[specialize] map (i : USize) (bs : Array NonScalar) : m (Array PNonScalar.{v}) := do
    if i < sz then
     let v    := bs.uget i lcProof
     -- Replace bs[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
     -- Note: we assume that arrays have a uniform representation irrespective
     -- of the element type, and that it is valid to store `box(0)` in any array.
     let bs'    := bs.uset i default lcProof
     let vNew ← f (unsafeCast v)
     map (i+1) (bs'.uset i (unsafeCast vNew) lcProof)
    else
     pure (unsafeCast bs)
  unsafeCast <| map 0 (unsafeCast as)

/-- Reference implementation for `mapM` -/
@[implemented_by mapMUnsafe]
def mapM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) (as : Array α) : m (Array β) :=
  -- Note: we cannot use `foldlM` here for the reference implementation because this calls
  -- `bind` and `pure` too many times. (We are not assuming `m` is a `LawfulMonad`)
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
    map (i : Nat) (bs : Array β) : m (Array β) := do
      if hlt : i < as.size then
        map (i+1) (bs.push (← f as[i]))
      else
        pure bs
  decreasing_by simp_wf; decreasing_trivial_pre_omega
  map 0 (mkEmpty as.size)

@[deprecated mapM (since := "2024-11-11")] abbrev sequenceMap := @mapM

/-- Variant of `mapIdxM` which receives the index `i` along with the bound `i < as.size`. -/
@[inline]
def mapFinIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → m β) : m (Array β) :=
  let rec @[specialize] map (i : Nat) (j : Nat) (inv : i + j = as.size) (bs : Array β) : m (Array β) := do
    match i, inv with
    | 0,    _  => pure bs
    | i+1, inv =>
      have j_lt : j < as.size := by
        rw [← inv, Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm]
        apply Nat.le_add_right
      have : i + (j + 1) = as.size := by rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
      map i (j+1) this (bs.push (← f j as[j] j_lt))
  map as.size 0 rfl (mkEmpty as.size)

@[inline]
def mapIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : Nat → α → m β) (as : Array α) : m (Array β) :=
  as.mapFinIdxM fun i a _ => f i a

@[inline]
def firstM {α : Type u} {m : Type v → Type w} [Alternative m] (f : α → m β) (as : Array α) : m β :=
  go 0
where
  go (i : Nat) : m β :=
    if hlt : i < as.size then
      f as[i] <|> go (i+1)
    else
      failure
  termination_by as.size - i
  decreasing_by exact Nat.sub_succ_lt_self as.size i hlt

@[inline]
def findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m (Option β)) (as : Array α) : m (Option β) := do
  for a in as do
    match (← f a) with
    | some b => return b
    | _      => pure ⟨⟩
  return none

/--
Note that the universe level is contrained to `Type` here,
to avoid having to have the predicate live in `p : α → m (ULift Bool)`.
-/
@[inline]
def findM? {α : Type} {m : Type → Type} [Monad m] (p : α → m Bool) (as : Array α) : m (Option α) := do
  for a in as do
    if (← p a) then
      return a
  return none

@[inline]
def findIdxM? [Monad m] (p : α → m Bool) (as : Array α) : m (Option Nat) := do
  let mut i := 0
  for a in as do
    if (← p a) then
      return some i
    i := i + 1
  return none

@[inline]
unsafe def anyMUnsafe {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  let rec @[specialize] any (i : USize) (stop : USize) : m Bool := do
    if i == stop then
      pure false
    else
      if (← p (as.uget i lcProof)) then
        pure true
      else
        any (i+1) stop
  if start < stop then
    let stop' := min stop as.size
    if start < stop' then
      any (USize.ofNat start) (USize.ofNat stop')
    else
      pure false
  else
    pure false

@[implemented_by anyMUnsafe]
def anyM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  let any (stop : Nat) (h : stop ≤ as.size) :=
    let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
    loop (j : Nat) : m Bool := do
      if hlt : j < stop then
        have : j < as.size := Nat.lt_of_lt_of_le hlt h
        if (← p as[j]) then
          pure true
        else
          loop (j+1)
      else
        pure false
      decreasing_by simp_wf; decreasing_trivial_pre_omega
    loop start
  if h : stop ≤ as.size then
    any stop h
  else
    any as.size (Nat.le_refl _)

@[inline]
def allM {α : Type u} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m Bool :=
  return !(← as.anyM (start := start) (stop := stop) fun v => return !(← p v))

@[inline]
def findSomeRevM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m (Option β)) (as : Array α) : m (Option β) :=
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
def findRevM? {α : Type} {m : Type → Type w} [Monad m] (p : α → m Bool) (as : Array α) : m (Option α) :=
  as.findSomeRevM? fun a => return if (← p a) then some a else none

@[inline]
protected def forM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := 0) (stop := as.size) : m PUnit :=
  as.foldlM (fun _ => f) ⟨⟩ start stop

instance : ForM m (Array α) α where
  forM xs f := Array.forM f xs

-- We simplify `Array.forM` to `forM`.
@[simp] theorem forM_eq_forM [Monad m] (f : α → m PUnit) :
    Array.forM f as 0 as.size = forM as f := rfl

@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := as.size) (stop := 0) : m PUnit :=
  as.foldrM (fun a _ => f a) ⟨⟩ start stop

@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β) (as : Array α) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM f init start stop

@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) (as : Array α) (start := as.size) (stop := 0) : β :=
  Id.run <| as.foldrM f init start stop

/-- Sum of an array.

`Array.sum #[a, b, c] = a + (b + (c + 0))` -/
@[inline]
def sum {α} [Add α] [Zero α] : Array α → α :=
  foldr (· + ·) 0

@[inline]
def countP {α : Type u} (p : α → Bool) (as : Array α) : Nat :=
  as.foldr (init := 0) fun a acc => bif p a then acc + 1 else acc

@[inline]
def count {α : Type u} [BEq α] (a : α) (as : Array α) : Nat :=
  countP (· == a) as

@[inline]
def map {α : Type u} {β : Type v} (f : α → β) (as : Array α) : Array β :=
  Id.run <| as.mapM f

instance : Functor Array where
  map := map

/-- Variant of `mapIdx` which receives the index as a `Fin as.size`. -/
@[inline]
def mapFinIdx {α : Type u} {β : Type v} (as : Array α) (f : (i : Nat) → α → (h : i < as.size) → β) : Array β :=
  Id.run <| as.mapFinIdxM f

@[inline]
def mapIdx {α : Type u} {β : Type v} (f : Nat → α → β) (as : Array α) : Array β :=
  Id.run <| as.mapIdxM f

/-- Turns `#[a, b]` into `#[(a, 0), (b, 1)]`. -/
def zipIdx (xs : Array α) (start := 0) : Array (α × Nat) :=
  xs.mapIdx fun i a => (a, start + i)

@[deprecated zipIdx (since := "2025-01-21")] abbrev zipWithIndex := @zipIdx

@[inline]
def find? {α : Type u} (p : α → Bool) (as : Array α) : Option α :=
  Id.run do
    for a in as do
      if p a then
        return a
    return none

@[inline]
def findSome? {α : Type u} {β : Type v} (f : α → Option β) (as : Array α) : Option β :=
  Id.run <| as.findSomeM? f

@[inline]
def findSome! {α : Type u} {β : Type v} [Inhabited β] (f : α → Option β) (xs : Array α) : β :=
  match xs.findSome? f with
  | some b => b
  | none   => panic! "failed to find element"

@[inline]
def findSomeRev? {α : Type u} {β : Type v} (f : α → Option β) (as : Array α) : Option β :=
  Id.run <| as.findSomeRevM? f

@[inline]
def findRev? {α : Type} (p : α → Bool) (as : Array α) : Option α :=
  Id.run <| as.findRevM? p

@[inline]
def findIdx? {α : Type u} (p : α → Bool) (as : Array α) : Option Nat :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  loop (j : Nat) :=
    if h : j < as.size then
      if p as[j] then some j else loop (j + 1)
    else none
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  loop 0

@[inline]
def findFinIdx? {α : Type u} (p : α → Bool) (as : Array α) : Option (Fin as.size) :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  loop (j : Nat) :=
    if h : j < as.size then
      if p as[j] then some ⟨j, h⟩ else loop (j + 1)
    else none
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  loop 0

theorem findIdx?_loop_eq_map_findFinIdx?_loop_val {xs : Array α} {p : α → Bool} {j} :
    findIdx?.loop p xs j = (findFinIdx?.loop p xs j).map (·.val) := by
  unfold findIdx?.loop
  unfold findFinIdx?.loop
  split <;> rename_i h
  case isTrue =>
    split
    case isTrue => simp
    case isFalse =>
      have : xs.size - (j + 1) < xs.size - j := Nat.sub_succ_lt_self xs.size j h
      rw [findIdx?_loop_eq_map_findFinIdx?_loop_val (j := j + 1)]
  case isFalse => simp
termination_by xs.size - j

theorem findIdx?_eq_map_findFinIdx?_val {xs : Array α} {p : α → Bool} :
    xs.findIdx? p = (xs.findFinIdx? p).map (·.val) := by
  simp [findIdx?, findFinIdx?, findIdx?_loop_eq_map_findFinIdx?_loop_val]

@[inline]
def findIdx (p : α → Bool) (as : Array α) : Nat := (as.findIdx? p).getD as.size

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def idxOfAux [BEq α] (xs : Array α) (v : α) (i : Nat) : Option (Fin xs.size) :=
  if h : i < xs.size then
    if xs[i] == v then some ⟨i, h⟩
    else idxOfAux xs v (i+1)
  else none
decreasing_by simp_wf; decreasing_trivial_pre_omega

@[deprecated idxOfAux (since := "2025-01-29")]
abbrev indexOfAux := @idxOfAux

def finIdxOf? [BEq α] (xs : Array α) (v : α) : Option (Fin xs.size) :=
  idxOfAux xs v 0

@[deprecated "`Array.indexOf?` has been deprecated, use `idxOf?` or `finIdxOf?` instead." (since := "2025-01-29")]
abbrev indexOf? := @finIdxOf?

/-- Returns the index of the first element equal to `a`, or the length of the array otherwise. -/
def idxOf [BEq α] (a : α) : Array α → Nat := findIdx (· == a)

def idxOf? [BEq α] (xs : Array α) (v : α) : Option Nat :=
  (xs.finIdxOf? v).map (·.val)

@[deprecated idxOf? (since := "2024-11-20")]
def getIdx? [BEq α] (xs : Array α) (v : α) : Option Nat :=
  xs.findIdx? fun a => a == v

@[inline]
def any (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.anyM p start stop

@[inline]
def all (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.allM p start stop

/-- `as.contains a` is true if there is some element `b` in `as` such that `a == b`. -/
def contains [BEq α] (as : Array α) (a : α) : Bool :=
  as.any (a == ·)

/--
Variant of `Array.contains` with arguments reversed.

For verification purposes, we simplify this to `contains`.
-/
def elem [BEq α] (a : α) (as : Array α) : Bool :=
  as.contains a

/-- Convert a `Array α` into an `List α`. This is O(n) in the size of the array.  -/
-- This function is exported to C, where it is called by `Array.toList`
-- (the projection) to implement this functionality.
@[export lean_array_to_list_impl]
def toListImpl (as : Array α) : List α :=
  as.foldr List.cons []

/-- Prepends an `Array α` onto the front of a list.  Equivalent to `as.toList ++ l`. -/
@[inline]
def toListAppend (as : Array α) (l : List α) : List α :=
  as.foldr List.cons l

protected def append (as : Array α) (bs : Array α) : Array α :=
  bs.foldl (init := as) fun xs v => xs.push v

instance : Append (Array α) := ⟨Array.append⟩

protected def appendList (as : Array α) (bs : List α) : Array α :=
  bs.foldl (init := as) fun xs v => xs.push v

instance : HAppend (Array α) (List α) (Array α) := ⟨Array.appendList⟩

@[inline]
def flatMapM [Monad m] (f : α → m (Array β)) (as : Array α) : m (Array β) :=
  as.foldlM (init := empty) fun bs a => do return bs ++ (← f a)

@[deprecated flatMapM (since := "2024-10-16")] abbrev concatMapM := @flatMapM

@[inline]
def flatMap (f : α → Array β) (as : Array α) : Array β :=
  as.foldl (init := empty) fun bs a => bs ++ f a

@[deprecated flatMap (since := "2024-10-16")] abbrev concatMap := @flatMap

/-- Joins array of array into a single array.

`flatten #[#[a₁, a₂, ⋯], #[b₁, b₂, ⋯], ⋯]` = `#[a₁, a₂, ⋯, b₁, b₂, ⋯]`
-/
@[inline] def flatten (xss : Array (Array α)) : Array α :=
  xss.foldl (init := empty) fun acc xs => acc ++ xs

def reverse (as : Array α) : Array α :=
  if h : as.size ≤ 1 then
    as
  else
    loop as 0 ⟨as.size - 1, Nat.pred_lt (mt (fun h : as.size = 0 => h ▸ by decide) h)⟩
where
  termination {i j : Nat} (h : i < j) : j - 1 - (i + 1) < j - i := by
    rw [Nat.sub_sub, Nat.add_comm]
    exact Nat.lt_of_le_of_lt (Nat.pred_le _) (Nat.sub_succ_lt_self _ _ h)
  loop (as : Array α) (i : Nat) (j : Fin as.size) :=
    if h : i < j then
      have := termination h
      let as := as.swap i j (Nat.lt_trans h j.2)
      have : j-1 < as.size := by rw [size_swap]; exact Nat.lt_of_le_of_lt (Nat.pred_le _) j.2
      loop as (i+1) ⟨j-1, this⟩
    else
      as

@[inline]
def filter (p : α → Bool) (as : Array α) (start := 0) (stop := as.size) : Array α :=
  as.foldl (init := #[]) (start := start) (stop := stop) fun acc a =>
    if p a then acc.push a else acc

@[inline]
def filterM {α : Type} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m (Array α) :=
  as.foldlM (init := #[]) (start := start) (stop := stop) fun acc a => do
    if (← p a) then return acc.push a else return acc

@[inline]
def filterRevM {α : Type} [Monad m] (p : α → m Bool) (as : Array α) (start := as.size) (stop := 0) : m (Array α) :=
  reverse <$> as.foldrM (init := #[]) (start := start) (stop := stop) fun a acc => do
    if (← p a) then return acc.push a else return acc

@[specialize]
def filterMapM [Monad m] (f : α → m (Option β)) (as : Array α) (start := 0) (stop := as.size) : m (Array β) :=
  as.foldlM (init := #[]) (start := start) (stop := stop) fun bs a => do
    match (← f a) with
    | some b => pure (bs.push b)
    | none   => pure bs

@[inline]
def filterMap (f : α → Option β) (as : Array α) (start := 0) (stop := as.size) : Array β :=
  Id.run <| as.filterMapM f (start := start) (stop := stop)

@[specialize]
def getMax? (as : Array α) (lt : α → α → Bool) : Option α :=
  if h : 0 < as.size then
    let a0 := as[0]
    some <| as.foldl (init := a0) (start := 1) fun best a =>
      if lt best a then a else best
  else
    none

@[inline]
def partition (p : α → Bool) (as : Array α) : Array α × Array α := Id.run do
  let mut bs := #[]
  let mut cs := #[]
  for a in as do
    if p a then
      bs := bs.push a
    else
      cs := cs.push a
  return (bs, cs)

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def popWhile (p : α → Bool) (as : Array α) : Array α :=
  if h : as.size > 0 then
    if p (as[as.size - 1]'(Nat.sub_lt h (by decide))) then
      popWhile p as.pop
    else
      as
  else
    as
decreasing_by simp_wf; decreasing_trivial_pre_omega

@[simp] theorem popWhile_empty (p : α → Bool) :
    popWhile p #[] = #[] := by
  simp [popWhile]

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  go (i : Nat) (acc : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (acc.push a)
      else
        acc
    else
      acc
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  go 0 #[]

/--
Remove the element at a given index from an array without a runtime bounds checks,
using a `Nat` index and a tactic-provided bound.

This function takes worst case O(n) time because
it has to backshift all elements at positions greater than `i`.-/
@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def eraseIdx (xs : Array α) (i : Nat) (h : i < xs.size := by get_elem_tactic) : Array α :=
  if h' : i + 1 < xs.size then
    let xs' := xs.swap (i + 1) i
    xs'.eraseIdx (i + 1) (by simp [xs', h'])
  else
    xs.pop
termination_by xs.size - i
decreasing_by simp_wf; exact Nat.sub_succ_lt_self _ _ h

-- This is required in `Lean.Data.PersistentHashMap`.
@[simp] theorem size_eraseIdx (xs : Array α) (i : Nat) (h) : (xs.eraseIdx i h).size = xs.size - 1 := by
  induction xs, i, h using Array.eraseIdx.induct with
  | @case1 xs i h h' xs' ih =>
    unfold eraseIdx
    simp +zetaDelta [h', xs', ih]
  | case2 xs i h h' =>
    unfold eraseIdx
    simp [h']

/-- Remove the element at a given index from an array, or do nothing if the index is out of bounds.

  This function takes worst case O(n) time because
  it has to backshift all elements at positions greater than `i`.-/
def eraseIdxIfInBounds (xs : Array α) (i : Nat) : Array α :=
  if h : i < xs.size then xs.eraseIdx i h else xs

/-- Remove the element at a given index from an array, or panic if the index is out of bounds.

This function takes worst case O(n) time because
it has to backshift all elements at positions greater than `i`. -/
def eraseIdx! (xs : Array α) (i : Nat) : Array α :=
  if h : i < xs.size then xs.eraseIdx i h else panic! "invalid index"

/-- Remove a specified element from an array, or do nothing if it is not present.

This function takes worst case O(n) time because
it has to backshift all later elements. -/
def erase [BEq α] (as : Array α) (a : α) : Array α :=
  match as.finIdxOf? a with
  | none   => as
  | some i => as.eraseIdx i

/-- Erase the first element that satisfies the predicate `p`.

This function takes worst case O(n) time because
it has to backshift all later elements. -/
def eraseP (as : Array α) (p : α → Bool) : Array α :=
  match as.findFinIdx? p with
  | none   => as
  | some i => as.eraseIdx i

/-- Insert element `a` at position `i`.

This function takes worst case O(n) time because
it has to swap the inserted element into place.
-/
@[inline] def insertIdx (as : Array α) (i : Nat) (a : α) (_ : i ≤ as.size := by get_elem_tactic) : Array α :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  loop (as : Array α) (j : Fin as.size) :=
    if i < j then
      let j' : Fin as.size := ⟨j-1, Nat.lt_of_le_of_lt (Nat.pred_le _) j.2⟩
      let as := as.swap j' j
      loop as ⟨j', by rw [size_swap]; exact j'.2⟩
    else
      as
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  let j := as.size
  let as := as.push a
  loop as ⟨j, size_push .. ▸ j.lt_succ_self⟩

@[deprecated insertIdx (since := "2024-11-20")] abbrev insertAt := @insertIdx

/-- Insert element `a` at position `i`. Panics if `i` is not `i ≤ as.size`. -/
def insertIdx! (as : Array α) (i : Nat) (a : α) : Array α :=
  if h : i ≤ as.size then
    insertIdx as i a
  else panic! "invalid index"

@[deprecated insertIdx! (since := "2024-11-20")] abbrev insertAt! := @insertIdx!

/-- Insert element `a` at position `i`, or do nothing if `as.size < i`. -/
def insertIdxIfInBounds (as : Array α) (i : Nat) (a : α) : Array α :=
  if h : i ≤ as.size then
    insertIdx as i a
  else
    as

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def isPrefixOfAux [BEq α] (as bs : Array α) (hle : as.size ≤ bs.size) (i : Nat) : Bool :=
  if h : i < as.size then
    let a := as[i]
    have : i < bs.size := Nat.lt_of_lt_of_le h hle
    let b := bs[i]
    if a == b then
      isPrefixOfAux as bs hle (i+1)
    else
      false
  else
    true
decreasing_by simp_wf; decreasing_trivial_pre_omega

/-- Return true iff `as` is a prefix of `bs`.
That is, `bs = as ++ t` for some `t : List α`.-/
def isPrefixOf [BEq α] (as bs : Array α) : Bool :=
  if h : as.size ≤ bs.size then
    isPrefixOfAux as bs h 0
  else
    false

@[semireducible, specialize] -- This is otherwise irreducible because it uses well-founded recursion.
def zipWithAux (as : Array α) (bs : Array β) (f : α → β → γ) (i : Nat) (cs : Array γ) : Array γ :=
  if h : i < as.size then
    let a := as[i]
    if h : i < bs.size then
      let b := bs[i]
      zipWithAux as bs f (i+1) <| cs.push <| f a b
    else
      cs
  else
    cs
decreasing_by simp_wf; decreasing_trivial_pre_omega

@[inline] def zipWith (f : α → β → γ) (as : Array α) (bs : Array β) : Array γ :=
  zipWithAux as bs f 0 #[]

def zip (as : Array α) (bs : Array β) : Array (α × β) :=
  zipWith Prod.mk as bs

def zipWithAll (f : Option α → Option β → γ) (as : Array α) (bs : Array β) : Array γ :=
  go as bs 0 #[]
where go (as : Array α) (bs : Array β) (i : Nat) (cs : Array γ) :=
  if i < max as.size bs.size then
    let a := as[i]?
    let b := bs[i]?
    go as bs (i+1) (cs.push (f a b))
  else
    cs
  termination_by max as.size bs.size - i
  decreasing_by simp_wf; decreasing_trivial_pre_omega

def unzip (as : Array (α × β)) : Array α × Array β :=
  as.foldl (init := (#[], #[])) fun (as, bs) (a, b) => (as.push a, bs.push b)

@[deprecated partition (since := "2024-11-06")]
def split (as : Array α) (p : α → Bool) : Array α × Array α :=
  as.foldl (init := (#[], #[])) fun (as, bs) a =>
    if p a then (as.push a, bs) else (as, bs.push a)

/-! ### Lexicographic ordering -/

instance instLT [LT α] : LT (Array α) := ⟨fun as bs => as.toList < bs.toList⟩
instance instLE [LT α] : LE (Array α) := ⟨fun as bs => as.toList ≤ bs.toList⟩

-- See `Init.Data.Array.Lex.Basic` for the boolean valued lexicographic comparator.

/-! ## Auxiliary functions used in metaprogramming.

We do not currently intend to provide verification theorems for these functions.
-/

/- ### reduceOption -/

/-- Drop `none`s from a Array, and replace each remaining `some a` with `a`. -/
@[inline] def reduceOption (as : Array (Option α)) : Array α :=
  as.filterMap id

/-! ### eraseReps -/

/--
`O(|l|)`. Erase repeated adjacent elements. Keeps the first occurrence of each run.
* `eraseReps #[1, 3, 2, 2, 2, 3, 5] = #[1, 3, 2, 3, 5]`
-/
def eraseReps {α} [BEq α] (as : Array α) : Array α :=
  if h : 0 < as.size then
    let ⟨last, acc⟩ := as.foldl (init := (as[0], #[])) fun ⟨last, acc⟩ a =>
      if a == last then ⟨last, acc⟩ else ⟨a, acc.push last⟩
    acc.push last
  else
    #[]

/-! ### allDiff -/

private def allDiffAuxAux [BEq α] (as : Array α) (a : α) : forall (i : Nat), i < as.size → Bool
  | 0,   _ => true
  | i+1, h =>
    have : i < as.size := Nat.lt_trans (Nat.lt_succ_self _) h;
    a != as[i] && allDiffAuxAux as a i this

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
private def allDiffAux [BEq α] (as : Array α) (i : Nat) : Bool :=
  if h : i < as.size then
    allDiffAuxAux as as[i] i h && allDiffAux as (i+1)
  else
    true
decreasing_by simp_wf; decreasing_trivial_pre_omega

def allDiff [BEq α] (as : Array α) : Bool :=
  allDiffAux as 0

/-! ### getEvenElems -/

@[inline] def getEvenElems (as : Array α) : Array α :=
  (·.2) <| as.foldl (init := (true, Array.empty)) fun (even, acc) a =>
    if even then
      (false, acc.push a)
    else
      (true, acc)

/-! ### Repr and ToString -/

instance {α : Type u} [Repr α] : Repr (Array α) where
  reprPrec xs _ :=
    let _ : Std.ToFormat α := ⟨repr⟩
    if xs.size == 0 then
      "#[]"
    else
      Std.Format.bracketFill "#[" (Std.Format.joinSep (toList xs) ("," ++ Std.Format.line)) "]"

instance [ToString α] : ToString (Array α) where
  toString xs := "#" ++ toString xs.toList

end Array

export Array (mkArray)
