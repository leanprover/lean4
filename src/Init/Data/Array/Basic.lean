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
import Init.Data.List.ToArray
import Init.Data.Array.Set
universe u v w

/-! ### Array literal syntax -/

syntax "#[" withoutPosition(sepBy(term, ", ")) "]" : term

macro_rules
  | `(#[ $elems,* ]) => `(List.toArray [ $elems,* ])

variable {α : Type u}

namespace Array

@[deprecated toList (since := "2024-10-13")] abbrev data := @toList

/-! ### Preliminary theorems -/

@[simp] theorem size_set (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (set a i v h).size = a.size :=
  List.length_set ..

@[simp] theorem size_push (a : Array α) (v : α) : (push a v).size = a.size + 1 :=
  List.length_concat ..

theorem ext (a b : Array α)
    (h₁ : a.size = b.size)
    (h₂ : (i : Nat) → (hi₁ : i < a.size) → (hi₂ : i < b.size) → a[i] = b[i])
    : a = b := by
  let rec extAux (a b : List α)
      (h₁ : a.length = b.length)
      (h₂ : (i : Nat) → (hi₁ : i < a.length) → (hi₂ : i < b.length) → a.get ⟨i, hi₁⟩ = b.get ⟨i, hi₂⟩)
      : a = b := by
    induction a generalizing b with
    | nil =>
      cases b with
      | nil       => rfl
      | cons b bs => rw [List.length_cons] at h₁; injection h₁
    | cons a as ih =>
      cases b with
      | nil => rw [List.length_cons] at h₁; injection h₁
      | cons b bs =>
        have hz₁ : 0 < (a::as).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have hz₂ : 0 < (b::bs).length := by rw [List.length_cons]; apply Nat.zero_lt_succ
        have headEq : a = b := h₂ 0 hz₁ hz₂
        have h₁' : as.length = bs.length := by rw [List.length_cons, List.length_cons] at h₁; injection h₁
        have h₂' : (i : Nat) → (hi₁ : i < as.length) → (hi₂ : i < bs.length) → as.get ⟨i, hi₁⟩ = bs.get ⟨i, hi₂⟩ := by
          intro i hi₁ hi₂
          have hi₁' : i+1 < (a::as).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have hi₂' : i+1 < (b::bs).length := by rw [List.length_cons]; apply Nat.succ_lt_succ; assumption
          have : (a::as).get ⟨i+1, hi₁'⟩ = (b::bs).get ⟨i+1, hi₂'⟩ := h₂ (i+1) hi₁' hi₂'
          apply this
        have tailEq : as = bs := ih bs h₁' h₂'
        rw [headEq, tailEq]
  cases a; cases b
  apply congrArg
  apply extAux
  assumption
  assumption

theorem ext' {as bs : Array α} (h : as.toList = bs.toList) : as = bs := by
  cases as; cases bs; simp at h; rw [h]

@[simp] theorem toArrayAux_eq (as : List α) (acc : Array α) : (as.toArrayAux acc).toList = acc.toList ++ as := by
  induction as generalizing acc <;> simp [*, List.toArrayAux, Array.push, List.append_assoc, List.concat_eq_append]

@[simp] theorem toList_toArray (as : List α) : as.toArray.toList = as := rfl

@[simp] theorem size_toArray (as : List α) : as.toArray.size = as.length := by simp [size]

@[simp] theorem getElem_toList {a : Array α} {i : Nat} (h : i < a.size) : a.toList[i] = a[i] := rfl

/-- `a ∈ as` is a predicate which asserts that `a` is in the array `as`. -/
-- NB: This is defined as a structure rather than a plain def so that a lemma
-- like `sizeOf_lt_of_mem` will not apply with no actual arrays around.
structure Mem (as : Array α) (a : α) : Prop where
  val : a ∈ as.toList

instance : Membership α (Array α) where
  mem := Mem

theorem mem_def {a : α} {as : Array α} : a ∈ as ↔ a ∈ as.toList :=
  ⟨fun | .mk h => h, Array.Mem.mk⟩

@[simp] theorem getElem_mem {l : Array α} {i : Nat} (h : i < l.size) : l[i] ∈ l := by
  rw [Array.mem_def, ← getElem_toList]
  apply List.getElem_mem

end Array

namespace List

@[simp] theorem toArray_toList (a : Array α) : a.toList.toArray = a := rfl

@[simp] theorem getElem_toArray {a : List α} {i : Nat} (h : i < a.toArray.size) :
    a.toArray[i] = a[i]'(by simpa using h) := rfl

@[simp] theorem getElem?_toArray {a : List α} {i : Nat} : a.toArray[i]? = a[i]? := rfl

@[simp] theorem getElem!_toArray [Inhabited α] {a : List α} {i : Nat} :
    a.toArray[i]! = a[i]! := rfl

end List

namespace Array

@[deprecated toList_toArray (since := "2024-09-09")] abbrev data_toArray := @toList_toArray

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
def uset (a : Array α) (i : USize) (v : α) (h : i.toNat < a.size) : Array α :=
  a.set i.toNat v h

@[extern "lean_array_pop"]
def pop (a : Array α) : Array α where
  toList := a.toList.dropLast

@[simp] theorem size_pop (a : Array α) : a.pop.size = a.size - 1 := by
  match a with
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
def swap (a : Array α) (i j : @& Fin a.size) : Array α :=
  let v₁ := a[i]
  let v₂ := a[j]
  let a'  := a.set i v₂
  a'.set j v₁ (Nat.lt_of_lt_of_eq j.isLt (size_set a i v₂ _).symm)

@[simp] theorem size_swap (a : Array α) (i j : Fin a.size) : (a.swap i j).size = a.size := by
  show ((a.set i a[j]).set j a[i]
    (Nat.lt_of_lt_of_eq j.isLt (size_set a i a[j] _).symm)).size = a.size
  rw [size_set, size_set]

/--
Swaps two entries in an array, or returns the array unchanged if either index is out of bounds.

This will perform the update destructively provided that `a` has a reference
count of 1 when called.
-/
@[extern "lean_array_swap"]
def swap! (a : Array α) (i j : @& Nat) : Array α :=
  if h₁ : i < a.size then
  if h₂ : j < a.size then swap a ⟨i, h₁⟩ ⟨j, h₂⟩
  else a
  else a

/-! ### GetElem instance for `USize`, backed by `uget` -/

instance : GetElem (Array α) USize α fun xs i => i.toNat < xs.size where
  getElem xs i h := xs.uget i h

/-! ### Definitions -/

instance : EmptyCollection (Array α) := ⟨Array.empty⟩
instance : Inhabited (Array α) where
  default := Array.empty

@[simp] def isEmpty (a : Array α) : Bool :=
  a.size = 0

@[specialize]
def isEqvAux (a b : Array α) (hsz : a.size = b.size) (p : α → α → Bool) :
    ∀ (i : Nat) (_ : i ≤ a.size), Bool
  | 0, _ => true
  | i+1, h =>
    p a[i] (b[i]'(hsz ▸ h)) && isEqvAux a b hsz p i (Nat.le_trans (Nat.le_add_right i 1) h)

@[inline] def isEqv (a b : Array α) (p : α → α → Bool) : Bool :=
  if h : a.size = b.size then
    isEqvAux a b h p a.size (Nat.le_refl a.size)
  else
    false

instance [BEq α] : BEq (Array α) :=
  ⟨fun a b => isEqv a b BEq.beq⟩

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
  n.fold (flip Array.push) (mkEmpty n)

def singleton (v : α) : Array α :=
  mkArray 1 v

def back! [Inhabited α] (a : Array α) : α :=
  a.get! (a.size - 1)

@[deprecated back! (since := "2024-10-31")] abbrev back := @back!

def get? (a : Array α) (i : Nat) : Option α :=
  if h : i < a.size then some a[i] else none

def back? (a : Array α) : Option α :=
  a[a.size - 1]?

@[inline] def swapAt (a : Array α) (i : Fin a.size) (v : α) : α × Array α :=
  let e := a[i]
  let a := a.set i v
  (e, a)

@[inline]
def swapAt! (a : Array α) (i : Nat) (v : α) : α × Array α :=
  if h : i < a.size then
    swapAt a ⟨i, h⟩ v
  else
    have : Inhabited (α × Array α) := ⟨(v, a)⟩
    panic! ("index " ++ toString i ++ " out of bounds")

/-- `take a n` returns the first `n` elements of `a`. -/
def take (a : Array α) (n : Nat) : Array α :=
  let rec loop
    | 0,   a => a
    | n+1, a => loop n a.pop
  loop (a.size - n) a

@[deprecated take (since := "2024-10-22")] abbrev shrink := @take

@[inline]
unsafe def modifyMUnsafe [Monad m] (a : Array α) (i : Nat) (f : α → m α) : m (Array α) := do
  if h : i < a.size then
    let v                := a[i]
    -- Replace a[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
    -- Note: we assume that arrays have a uniform representation irrespective
    -- of the element type, and that it is valid to store `box(0)` in any array.
    let a'               := a.set i (unsafeCast ())
    let v ← f v
    pure <| a'.set i v (Nat.lt_of_lt_of_eq h (size_set a ..).symm)
  else
    pure a

@[implemented_by modifyMUnsafe]
def modifyM [Monad m] (a : Array α) (i : Nat) (f : α → m α) : m (Array α) := do
  if h : i < a.size then
    let v   := a[i]
    let v ← f v
    pure <| a.set i v
  else
    pure a

@[inline]
def modify (a : Array α) (i : Nat) (f : α → α) : Array α :=
  Id.run <| modifyM a i f

@[inline]
def modifyOp (self : Array α) (idx : Nat) (f : α → α) : Array α :=
  self.modify idx f

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
  let rec @[specialize] map (i : USize) (r : Array NonScalar) : m (Array PNonScalar.{v}) := do
    if i < sz then
     let v    := r.uget i lcProof
     -- Replace r[i] by `box(0)`.  This ensures that `v` remains unshared if possible.
     -- Note: we assume that arrays have a uniform representation irrespective
     -- of the element type, and that it is valid to store `box(0)` in any array.
     let r    := r.uset i default lcProof
     let vNew ← f (unsafeCast v)
     map (i+1) (r.uset i (unsafeCast vNew) lcProof)
    else
     pure (unsafeCast r)
  unsafeCast <| map 0 (unsafeCast as)

/-- Reference implementation for `mapM` -/
@[implemented_by mapMUnsafe]
def mapM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m β) (as : Array α) : m (Array β) :=
  -- Note: we cannot use `foldlM` here for the reference implementation because this calls
  -- `bind` and `pure` too many times. (We are not assuming `m` is a `LawfulMonad`)
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
    map (i : Nat) (r : Array β) : m (Array β) := do
      if hlt : i < as.size then
        map (i+1) (r.push (← f as[i]))
      else
        pure r
  decreasing_by simp_wf; decreasing_trivial_pre_omega
  map 0 (mkEmpty as.size)

/-- Variant of `mapIdxM` which receives the index as a `Fin as.size`. -/
@[inline]
def mapFinIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m]
    (as : Array α) (f : Fin as.size → α → m β) : m (Array β) :=
  let rec @[specialize] map (i : Nat) (j : Nat) (inv : i + j = as.size) (bs : Array β) : m (Array β) := do
    match i, inv with
    | 0,    _  => pure bs
    | i+1, inv =>
      have j_lt : j < as.size := by
        rw [← inv, Nat.add_assoc, Nat.add_comm 1 j, Nat.add_comm]
        apply Nat.le_add_right
      have : i + (j + 1) = as.size := by rw [← inv, Nat.add_comm j 1, Nat.add_assoc]
      map i (j+1) this (bs.push (← f ⟨j, j_lt⟩ (as.get j j_lt)))
  map as.size 0 rfl (mkEmpty as.size)

@[inline]
def mapIdxM {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : Nat → α → m β) (as : Array α) : m (Array β) :=
  as.mapFinIdxM fun i a => f i a

@[inline]
def findSomeM? {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (f : α → m (Option β)) (as : Array α) : m (Option β) := do
  for a in as do
    match (← f a) with
    | some b => return b
    | _      => pure ⟨⟩
  return none

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
def forM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := 0) (stop := as.size) : m PUnit :=
  as.foldlM (fun _ => f) ⟨⟩ start stop

@[inline]
def forRevM {α : Type u} {m : Type v → Type w} [Monad m] (f : α → m PUnit) (as : Array α) (start := as.size) (stop := 0) : m PUnit :=
  as.foldrM (fun a _ => f a) ⟨⟩ start stop

@[inline]
def foldl {α : Type u} {β : Type v} (f : β → α → β) (init : β) (as : Array α) (start := 0) (stop := as.size) : β :=
  Id.run <| as.foldlM f init start stop

@[inline]
def foldr {α : Type u} {β : Type v} (f : α → β → β) (init : β) (as : Array α) (start := as.size) (stop := 0) : β :=
  Id.run <| as.foldrM f init start stop

@[inline]
def map {α : Type u} {β : Type v} (f : α → β) (as : Array α) : Array β :=
  Id.run <| as.mapM f

/-- Variant of `mapIdx` which receives the index as a `Fin as.size`. -/
@[inline]
def mapFinIdx {α : Type u} {β : Type v} (as : Array α) (f : Fin as.size → α → β) : Array β :=
  Id.run <| as.mapFinIdxM f

@[inline]
def mapIdx {α : Type u} {β : Type v} (f : Nat → α → β) (as : Array α) : Array β :=
  Id.run <| as.mapIdxM f

/-- Turns `#[a, b]` into `#[(a, 0), (b, 1)]`. -/
def zipWithIndex (arr : Array α) : Array (α × Nat) :=
  arr.mapIdx fun i a => (a, i)

@[inline]
def find? {α : Type} (p : α → Bool) (as : Array α) : Option α :=
  Id.run <| as.findM? p

@[inline]
def findSome? {α : Type u} {β : Type v} (f : α → Option β) (as : Array α) : Option β :=
  Id.run <| as.findSomeM? f

@[inline]
def findSome! {α : Type u} {β : Type v} [Inhabited β] (f : α → Option β) (a : Array α) : β :=
  match a.findSome? f with
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

def getIdx? [BEq α] (a : Array α) (v : α) : Option Nat :=
  a.findIdx? fun a => a == v

@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def indexOfAux [BEq α] (a : Array α) (v : α) (i : Nat) : Option (Fin a.size) :=
  if h : i < a.size then
    if a[i] == v then some ⟨i, h⟩
    else indexOfAux a v (i+1)
  else none
decreasing_by simp_wf; decreasing_trivial_pre_omega

def indexOf? [BEq α] (a : Array α) (v : α) : Option (Fin a.size) :=
  indexOfAux a v 0

@[inline]
def any (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.anyM p start stop

@[inline]
def all (as : Array α) (p : α → Bool) (start := 0) (stop := as.size) : Bool :=
  Id.run <| as.allM p start stop

def contains [BEq α] (as : Array α) (a : α) : Bool :=
  as.any (· == a)

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
  bs.foldl (init := as) fun r v => r.push v

instance : Append (Array α) := ⟨Array.append⟩

protected def appendList (as : Array α) (bs : List α) : Array α :=
  bs.foldl (init := as) fun r v => r.push v

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
@[inline] def flatten (as : Array (Array α)) : Array α :=
  as.foldl (init := empty) fun r a => r ++ a

@[inline]
def filter (p : α → Bool) (as : Array α) (start := 0) (stop := as.size) : Array α :=
  as.foldl (init := #[]) (start := start) (stop := stop) fun r a =>
    if p a then r.push a else r

@[inline]
def filterM {α : Type} [Monad m] (p : α → m Bool) (as : Array α) (start := 0) (stop := as.size) : m (Array α) :=
  as.foldlM (init := #[]) (start := start) (stop := stop) fun r a => do
    if (← p a) then return r.push a else return r

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
      let as := as.swap ⟨i, Nat.lt_trans h j.2⟩ j
      have : j-1 < as.size := by rw [size_swap]; exact Nat.lt_of_le_of_lt (Nat.pred_le _) j.2
      loop as (i+1) ⟨j-1, this⟩
    else
      as

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

def takeWhile (p : α → Bool) (as : Array α) : Array α :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  go (i : Nat) (r : Array α) : Array α :=
    if h : i < as.size then
      let a := as[i]
      if p a then
        go (i+1) (r.push a)
      else
        r
    else
      r
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  go 0 #[]

/-- Remove the element at a given index from an array without bounds checks, using a `Fin` index.

  This function takes worst case O(n) time because
  it has to backshift all elements at positions greater than `i`.-/
@[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
def feraseIdx (a : Array α) (i : Fin a.size) : Array α :=
  if h : i.val + 1 < a.size then
    let a' := a.swap ⟨i.val + 1, h⟩ i
    let i' : Fin a'.size := ⟨i.val + 1, by simp [a', h]⟩
    a'.feraseIdx i'
  else
    a.pop
termination_by a.size - i.val
decreasing_by simp_wf; exact Nat.sub_succ_lt_self _ _ i.isLt

-- This is required in `Lean.Data.PersistentHashMap`.
@[simp] theorem size_feraseIdx (a : Array α) (i : Fin a.size) : (a.feraseIdx i).size = a.size - 1 := by
  induction a, i using Array.feraseIdx.induct with
  | @case1 a i h a' _ ih =>
    unfold feraseIdx
    simp [h, a', ih]
  | case2 a i h =>
    unfold feraseIdx
    simp [h]

/-- Remove the element at a given index from an array, or do nothing if the index is out of bounds.

  This function takes worst case O(n) time because
  it has to backshift all elements at positions greater than `i`.-/
def eraseIdx (a : Array α) (i : Nat) : Array α :=
  if h : i < a.size then a.feraseIdx ⟨i, h⟩ else a

def erase [BEq α] (as : Array α) (a : α) : Array α :=
  match as.indexOf? a with
  | none   => as
  | some i => as.feraseIdx i

/-- Insert element `a` at position `i`. -/
@[inline] def insertAt (as : Array α) (i : Fin (as.size + 1)) (a : α) : Array α :=
  let rec @[semireducible] -- This is otherwise irreducible because it uses well-founded recursion.
  loop (as : Array α) (j : Fin as.size) :=
    if i.1 < j then
      let j' := ⟨j-1, Nat.lt_of_le_of_lt (Nat.pred_le _) j.2⟩
      let as := as.swap j' j
      loop as ⟨j', by rw [size_swap]; exact j'.2⟩
    else
      as
    decreasing_by simp_wf; decreasing_trivial_pre_omega
  let j := as.size
  let as := as.push a
  loop as ⟨j, size_push .. ▸ j.lt_succ_self⟩

/-- Insert element `a` at position `i`. Panics if `i` is not `i ≤ as.size`. -/
def insertAt! (as : Array α) (i : Nat) (a : α) : Array α :=
  if h : i ≤ as.size then
    insertAt as ⟨i, Nat.lt_succ_of_le h⟩ a
  else panic! "invalid index"

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
def zipWithAux (f : α → β → γ) (as : Array α) (bs : Array β) (i : Nat) (cs : Array γ) : Array γ :=
  if h : i < as.size then
    let a := as[i]
    if h : i < bs.size then
      let b := bs[i]
      zipWithAux f as bs (i+1) <| cs.push <| f a b
    else
      cs
  else
    cs
decreasing_by simp_wf; decreasing_trivial_pre_omega

@[inline] def zipWith (as : Array α) (bs : Array β) (f : α → β → γ) : Array γ :=
  zipWithAux f as bs 0 #[]

def zip (as : Array α) (bs : Array β) : Array (α × β) :=
  zipWith as bs Prod.mk

def unzip (as : Array (α × β)) : Array α × Array β :=
  as.foldl (init := (#[], #[])) fun (as, bs) (a, b) => (as.push a, bs.push b)

@[deprecated partition (since := "2024-11-06")]
def split (as : Array α) (p : α → Bool) : Array α × Array α :=
  as.foldl (init := (#[], #[])) fun (as, bs) a =>
    if p a then (as.push a, bs) else (as, bs.push a)

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
    let ⟨last, r⟩ := as.foldl (init := (as[0], #[])) fun ⟨last, r⟩ a =>
      if a == last then ⟨last, r⟩ else ⟨a, r.push last⟩
    r.push last
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
  (·.2) <| as.foldl (init := (true, Array.empty)) fun (even, r) a =>
    if even then
      (false, r.push a)
    else
      (true, r)

/-! ### Repr and ToString -/

instance {α : Type u} [Repr α] : Repr (Array α) where
  reprPrec a _ :=
    let _ : Std.ToFormat α := ⟨repr⟩
    if a.size == 0 then
      "#[]"
    else
      Std.Format.bracketFill "#[" (Std.Format.joinSep (toList a) ("," ++ Std.Format.line)) "]"

instance [ToString α] : ToString (Array α) where
  toString a := "#" ++ toString a.toList

end Array

export Array (mkArray)
