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

/-! ## Alternative getters -/

/-! ### get! -/

/--
Returns the `i`-th element in the list (zero-based).

If the index is out of bounds (`i ≥ as.length`), this function panics when executed, and returns
`default`. See `get?` and `getD` for safer alternatives.
-/
def get! [Inhabited α] : (as : List α) → (i : Nat) → α
  | a::_,  0   => a
  | _::as, n+1 => get! as n
  | _,     _   => panic! "invalid index"

theorem get!_nil [Inhabited α] (n : Nat) : [].get! n = (default : α) := rfl
theorem get!_cons_succ [Inhabited α] (l : List α) (a : α) (n : Nat) :
    (a::l).get! (n+1) = get! l n := rfl
theorem get!_cons_zero [Inhabited α] (l : List α) (a : α) : (a::l).get! 0 = a := rfl

/-! ### getLast! -/

/--
Returns the last element in the list.

If the list is empty, this function panics when executed, and returns `default`.
See `getLast` and `getLastD` for safer alternatives.
-/
def getLast! [Inhabited α] : List α → α
  | []    => panic! "empty list"
  | a::as => getLast (a::as) (fun h => List.noConfusion h)

/-! ## Head and tail -/

/-! ### head! -/

/--
Returns the first element in the list.

If the list is empty, this function panics when executed, and returns `default`.
See `head` and `headD` for safer alternatives.
-/
def head! [Inhabited α] : List α → α
  | []   => panic! "empty list"
  | a::_ => a

/-! ### tail! -/

/--
Drops the first element of the list.

If the list is empty, this function panics when executed, and returns the empty list.
See `tail` and `tailD` for safer alternatives.
-/
def tail! : List α → List α
  | []    => panic! "empty list"
  | _::as => as

@[simp] theorem tail!_cons : @tail! α (a::l) = l := rfl

/-! ### partitionM -/

/--
Monadic generalization of `List.partition`.

This uses `Array.toList` and which isn't imported by `Init.Data.List.Basic` or `Init.Data.List.Control`.
```
def posOrNeg (x : Int) : Except String Bool :=
  if x > 0 then pure true
  else if x < 0 then pure false
  else throw "Zero is not positive or negative"

partitionM posOrNeg [-1, 2, 3] = Except.ok ([2, 3], [-1])
partitionM posOrNeg [0, 2, 3] = Except.error "Zero is not positive or negative"
```
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

/-! ### partitionMap -/

/--
Given a function `f : α → β ⊕ γ`, `partitionMap f l` maps the list by `f`
whilst partitioning the result into a pair of lists, `List β × List γ`,
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

/-! ### mapMono

This is a performance optimization for `List.mapM` that avoids allocating a new list when the result of each `f a` is a pointer equal value `a`.

For verification purposes, `List.mapMono = List.map`.
-/

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

/-! ## Additional lemmas required for bootstrapping `Array`. -/

theorem getElem_append_left {as bs : List α} (h : i < as.length) {h' : i < (as ++ bs).length} :
    (as ++ bs)[i] = as[i] := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with
    | zero => rfl
    | succ i => apply ih

theorem getElem_append_right {as bs : List α} {i : Nat} (h₁ : as.length ≤ i) {h₂} :
    (as ++ bs)[i]'h₂ =
      bs[i - as.length]'(by rw [length_append] at h₂; exact Nat.sub_lt_left_of_lt_add h₁ h₂) := by
  induction as generalizing i with
  | nil => trivial
  | cons a as ih =>
    cases i with simp [get, Nat.succ_sub_succ] <;> simp [Nat.succ_sub_succ] at h₁
    | succ i => apply ih; simp [h₁]

theorem get_last {as : List α} {i : Fin (length (as ++ [a]))} (h : ¬ i.1 < as.length) : (as ++ [a] : List _).get i = a := by
  cases i; rename_i i h'
  induction as generalizing i with
  | nil => cases i with
    | zero => simp [List.get]
    | succ => simp +arith at h'
  | cons a as ih =>
    cases i with simp at h
    | succ i => apply ih; simp [h]

theorem sizeOf_lt_of_mem [SizeOf α] {as : List α} (h : a ∈ as) : sizeOf a < sizeOf as := by
  induction h with
  | head => simp +arith
  | tail _ _ ih => exact Nat.lt_trans ih (by simp +arith)

/-- This tactic, added to the `decreasing_trivial` toolbox, proves that
`sizeOf a < sizeOf as` when `a ∈ as`, which is useful for well founded recursions
over a nested inductive like `inductive T | mk : List T → T`. -/
macro "sizeOf_list_dec" : tactic =>
  `(tactic| first
    | with_reducible apply sizeOf_lt_of_mem; assumption; done
    | with_reducible
        apply Nat.lt_of_lt_of_le (sizeOf_lt_of_mem ?h)
        case' h => assumption
      simp +arith)

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
  | [], c::cs    => have aux := congrArg length h; simp +arith at aux
  | a::as, []    => have aux := congrArg length h; simp +arith at aux
  | a::as, c::cs => injection h with h₁ h₂; subst h₁; rw [append_cancel_right h₂]

@[simp] theorem append_cancel_left_eq (as bs cs : List α) : (as ++ bs = as ++ cs) = (bs = cs) := by
  apply propext; apply Iff.intro
  next => apply append_cancel_left
  next => intro h; simp [h]

@[simp] theorem append_cancel_right_eq (as bs cs : List α) : (as ++ bs = cs ++ bs) = (as = cs) := by
  apply propext; apply Iff.intro
  next => apply append_cancel_right
  next => intro h; simp [h]

theorem sizeOf_get [SizeOf α] (as : List α) (i : Fin as.length) : sizeOf (as.get i) < sizeOf as := by
  match as, i with
  | a::as, ⟨0, _⟩  => simp +arith [get]
  | a::as, ⟨i+1, h⟩ =>
    have ih := sizeOf_get as ⟨i, Nat.le_of_succ_le_succ h⟩
    apply Nat.lt_trans ih
    simp +arith

theorem not_lex_antisymm [DecidableEq α] {r : α → α → Prop} [DecidableRel r]
    (antisymm : ∀ x y : α, ¬ r x y → ¬ r y x → x = y)
    {as bs : List α} (h₁ : ¬ Lex r bs as) (h₂ : ¬ Lex r as bs) : as = bs :=
  match as, bs with
  | [],    []    => rfl
  | [],    _::_ => False.elim <| h₂ (List.Lex.nil ..)
  | _::_, []    => False.elim <| h₁ (List.Lex.nil ..)
  | a::as, b::bs => by
    by_cases hab : r a b
    · exact False.elim <| h₂ (List.Lex.rel hab)
    · by_cases eq : a = b
      · subst eq
        have h₁ : ¬ Lex r bs as := fun h => h₁ (List.Lex.cons h)
        have h₂ : ¬ Lex r as bs := fun h => h₂ (List.Lex.cons h)
        simp [not_lex_antisymm antisymm h₁ h₂]
      · exfalso
        by_cases hba : r b a
        · exact h₁ (Lex.rel hba)
        · exact eq (antisymm _ _ hab hba)

protected theorem le_antisymm [DecidableEq α] [LT α] [DecidableLT α]
    [i : Std.Antisymm (¬ · < · : α → α → Prop)]
    {as bs : List α} (h₁ : as ≤ bs) (h₂ : bs ≤ as) : as = bs :=
  not_lex_antisymm i.antisymm h₁ h₂

instance [DecidableEq α] [LT α] [DecidableLT α]
    [s : Std.Antisymm (¬ · < · : α → α → Prop)] :
    Std.Antisymm (· ≤ · : List α → List α → Prop) where
  antisymm _ _ h₁ h₂ := List.le_antisymm h₁ h₂

end List
