/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import Init.Data.Nat.Linear

universe u

namespace List
/-! The following functions can't be defined at `Init.Data.List.Basic`, because they depend on `Init.Util`,
   and `Init.Util` depends on `Init.Data.List.Basic`. -/

/--
Returns the `i`-th element in the list (zero-based).

If the index is out of bounds (`i ≥ as.length`), this function panics when executed, and returns
`default`. See `get?` and `getD` for safer alternatives.
-/
def get! [Inhabited α] : (as : List α) → (i : Nat) → α
  | a::_,  0   => a
  | _::as, n+1 => get! as n
  | _,     _   => panic! "invalid index"

/--
Returns the `i`-th element in the list (zero-based).

If the index is out of bounds (`i ≥ as.length`), this function returns `.none`
Also see `getD` and `get!`.
-/
def get? : (as : List α) → (i : Nat) → Option α
  | a::_,  0   => some a
  | _::as, n+1 => get? as n
  | _,     _   => none

/--
Returns the `i`-th element in the list (zero-based).

If the index is out of bounds (`i ≥ as.length`), this function returns `a₀`.
Also see `get?` and `get!`.
-/
def getD (as : List α) (i : Nat) (a₀ : α) : α :=
  (as.get? i).getD a₀

/--
Returns the first element in the list.

If the the list is empty, this function panics when executed, and returns `default`.
See `head` and `headD` for safer alternatives.
-/
def head! [Inhabited α] : List α → α
  | []   => panic! "empty list"
  | a::_ => a

/--
Returns the first element in the list.

If the the list is empty, this function returns `.none`.
Also see `headD` and `head!`.
-/
def head? : List α → Option α
  | []   => none
  | a::_ => some a

/--
Returns the first element in the list.

If the the list is empty, this function returns `a₀`.
Also see `head?` and `head!`.
-/
def headD : (as : List α) → (a₀ : α) → α
  | [],   a₀ => a₀
  | a::_, _  => a

/--
Returns the first element of a non-empty list.
-/
def head : (as : List α) → as ≠ [] → α
  | a::_, _ => a

/--
Drops the first element of the list.

If the the list is empty, this function panics when executed, and returns the empty list.
See `tail` and `tailD` for safer alternatives.
-/
def tail! : List α → List α
  | []    => panic! "empty list"
  | _::as => as

/--
Drops the first element of the list.

If the the list is empty, this function returns `.none`.
Also see `tailD` and `tail!`.
-/
def tail? : List α → Option (List α)
  | []    => none
  | _::as => some as

/--
Drops the first element of the list.

If the the list is empty, this function returns `as₀`.
Also see `head?` and `head!`.
-/
def tailD : List α → List α → List α
  | [],   as₀ => as₀
  | _::as, _  => as

/--
Returns the last element of a non-empty list.
-/
def getLast : ∀ (as : List α), as ≠ [] → α
  | [],       h => absurd rfl h
  | [a],      _ => a
  | _::b::as, _ => getLast (b::as) (fun h => List.noConfusion h)

/--
Returns the last element in the list.

If the the list is empty, this function panics when executed, and returns `default`.
See `last` and `lastD` for safer alternatives.
-/
def getLast! [Inhabited α] : List α → α
  | []    => panic! "empty list"
  | a::as => getLast (a::as) (fun h => List.noConfusion h)

/--
Returns the last element in the list.

If the the list is empty, this function returns `.none`.
Also see `lastD` and `last!`.
-/
def getLast? : List α → Option α
  | []    => none
  | a::as => some (getLast (a::as) (fun h => List.noConfusion h))

/--
Returns the last element in the list.

If the the list is empty, this function returns `a₀`.
Also see `last?` and `last!`.
-/
def getLastD : (as : List α) → (a₀ : α) → α
  | [],   a₀ => a₀
  | a::as, _ => getLast (a::as) (fun h => List.noConfusion h)

def rotateLeft (xs : List α) (n : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let n := n % len
    let b := xs.take n
    let e := xs.drop n
    e ++ b

def rotateRight (xs : List α) (n : Nat := 1) : List α :=
  let len := xs.length
  if len ≤ 1 then
    xs
  else
    let n := len - n % len
    let b := xs.take n
    let e := xs.drop n
    e ++ b

theorem get_append_left (as bs : List α) (h : i < as.length) {h'} : (as ++ bs).get ⟨i, h'⟩ = as.get ⟨i, h⟩ := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i => apply ih

theorem get_append_right (as bs : List α) (h : ¬ i < as.length) {h' h''} : (as ++ bs).get ⟨i, h'⟩ = bs.get ⟨i - as.length, h''⟩ := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with simp [get, Nat.succ_sub_succ] <;> simp_arith [Nat.succ_sub_succ] at h
    | succ i => apply ih; simp_arith [h]

theorem get_last {as : List α} {i : Fin (length (as ++ [a]))} (h : ¬ i.1 < as.length) : (as ++ [a] : List _).get i = a := by
  cases i; rename_i i h'
  induction as generalizing i with
  | nil => cases i with
    | zero => simp [List.get]
    | succ => simp_arith at h'
  | cons a as ih =>
    cases i with simp_arith at h
    | succ i => apply ih; simp_arith [h]

theorem sizeOf_lt_of_mem [SizeOf α] {as : List α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  induction h with
  | head => simp_arith
  | tail _ _ ih => exact Nat.lt_trans ih (by simp_arith)

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf a < sizeOf as` when `a ∈ as`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : List T → T`. -/
macro "sizeOf_list_dec" : tactic =>
  `(tactic| first
    | apply sizeOf_lt_of_mem; assumption; done
    | apply Nat.lt_trans (sizeOf_lt_of_mem ?h)
      case' h => assumption
      simp_arith)

macro_rules | `(tactic| decreasing_trivial) => `(tactic| sizeOf_list_dec)

theorem append_cancel_left {as bs cs : List α} (h : as ++ bs = as ++ cs) : bs = cs := by
  induction as with
  | nil => assumption
  | cons a as ih =>
    injection h with _ h
    exact ih h

theorem append_cancel_right {as bs cs : List α} (h : as ++ bs = cs ++ bs) : as = cs := by
  match as, cs with
  | [], []       => rfl
  | [], c::cs    => have aux := congrArg length h; simp_arith at aux
  | a::as, []    => have aux := congrArg length h; simp_arith at aux
  | a::as, c::cs => injection h with h₁ h₂; subst h₁; rw [append_cancel_right h₂]

@[simp] theorem append_cancel_left_eq (as bs cs : List α) : (as ++ bs = as ++ cs) = (bs = cs) := by
  apply propext; apply Iff.intro
  next => apply append_cancel_left
  next => intro h; simp [h]

@[simp] theorem append_cancel_right_eq (as bs cs : List α) : (as ++ bs = cs ++ bs) = (as = cs) := by
  apply propext; apply Iff.intro
  next => apply append_cancel_right
  next => intro h; simp [h]

@[simp] theorem sizeOf_get [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := by
  match as, i with
  | a::as, ⟨0, _⟩  => simp_arith [get]
  | a::as, ⟨i+1, h⟩ =>
    have ih := sizeOf_get as ⟨i, Nat.le_of_succ_le_succ h⟩
    apply Nat.lt_trans ih
    simp_arith

theorem le_antisymm [LT α] [s : Antisymm (¬ · < · : α → α → Prop)] {as bs : List α} (h₁ : as ≤ bs) (h₂ : bs ≤ as) : as = bs :=
  match as, bs with
  | [],    []    => rfl
  | [],    b::bs => False.elim <| h₂ (List.lt.nil ..)
  | a::as, []    => False.elim <| h₁ (List.lt.nil ..)
  | a::as, b::bs => by
    by_cases hab : a < b
    · exact False.elim <| h₂ (List.lt.head _ _ hab)
    · by_cases hba : b < a
      · exact False.elim <| h₁ (List.lt.head _ _ hba)
      · have h₁ : as ≤ bs := fun h => h₁ (List.lt.tail hba hab h)
        have h₂ : bs ≤ as := fun h => h₂ (List.lt.tail hab hba h)
        have ih : as = bs := le_antisymm h₁ h₂
        have : a = b := s.antisymm hab hba
        simp [this, ih]

instance [LT α] [Antisymm (¬ · < · : α → α → Prop)] : Antisymm (· ≤ · : List α → List α → Prop) where
  antisymm h₁ h₂ := le_antisymm h₁ h₂

@[specialize] private unsafe def mapMonoMImp [Monad m] (as : List α) (f : α → m α) : m (List α) := do
  match as with
  | [] => return as
  | b :: bs =>
    let b'  ← f b
    let bs' ← mapMonoMImp bs f
    if ptrEq b' b && ptrEq bs' bs then
      return as
    else
      return b' :: bs'

/--
Monomorphic `List.mapM`. The internal implementation uses pointer equality, and does not allocate a new list
if the result of each `f a` is a pointer equal value `a`.
-/
@[implemented_by mapMonoMImp] def mapMonoM [Monad m] (as : List α) (f : α → m α) : m (List α) :=
  match as with
  | [] => return []
  | a :: as => return (← f a) :: (← mapMonoM as f)

def mapMono (as : List α) (f : α → α) : List α :=
  Id.run <| as.mapMonoM f

/--
Monadic generalization of `List.partition`.

This uses `Array.toList` and which isn't imported by `Init.Data.List.Basic`.
-/
@[inline] def partitionM [Monad m] (p : α → m Bool) (l : List α) : m (List α × List α) :=
  go l #[] #[]
where
  /-- Auxiliary for `partitionM`:
  `partitionM.go p l acc₁ acc₂` returns `(acc₁.toList ++ left, acc₂.toList ++ right)`
  if `partitionM p l` returns `(left, right)`. -/
  @[specialize] go : List α → Array α → Array α → m (List α × List α)
  | [], acc₁, acc₂ => pure (acc₁.toList, acc₂.toList)
  | x :: xs, acc₁, acc₂ => do
    if ← p x then
      go xs (acc₁.push x) acc₂
    else
      go xs acc₁ (acc₂.push x)

/--
Given a function `f : α → β ⊕ γ`, `partitionMap f l` maps the list by `f`
whilst partitioning the result it into a pair of lists, `List β × List γ`,
partitioning the `.inl _` into the left list, and the `.inr _` into the right List.
```
partitionMap (id : Nat ⊕ Nat → Nat ⊕ Nat) [inl 0, inr 1, inl 2] = ([0, 2], [1])
```
-/
@[inline] def partitionMap (f : α → β ⊕ γ) (l : List α) : List β × List γ := go l #[] #[] where
  /-- Auxiliary for `partitionMap`:
  `partitionMap.go f l acc₁ acc₂ = (acc₁.toList ++ left, acc₂.toList ++ right)`
  if `partitionMap f l = (left, right)`. -/
  @[specialize] go : List α → Array β → Array γ → List β × List γ
  | [], acc₁, acc₂ => (acc₁.toList, acc₂.toList)
  | x :: xs, acc₁, acc₂ =>
    match f x with
    | .inl a => go xs (acc₁.push a) acc₂
    | .inr b => go xs acc₁ (acc₂.push b)

end List
