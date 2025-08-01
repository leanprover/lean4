/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian, Sebastian Ullrich
-/
module

prelude
public import Init.Data.String.Basic
public import Init.Data.Array.Basic
public import Init.Data.SInt.Basic
public import all Init.Data.Vector.Basic

public section

/--
The result of a comparison according to a total order.

The relationship between the compared items may be:
 * `Ordering.lt`: less than
 * `Ordering.eq`: equal
 * `Ordering.gt`: greater than
-/
inductive Ordering where
  /-- Less than. -/
  | lt
  /-- Equal. -/
  | eq
  /-- Greater than. -/
  | gt
deriving Inhabited, DecidableEq, Repr

namespace Ordering

/--
Swaps less-than and greater-than ordering results.

Examples:
 * `Ordering.lt.swap = Ordering.gt`
 * `Ordering.eq.swap = Ordering.eq`
 * `Ordering.gt.swap = Ordering.lt`
-/
@[inline, expose]
def swap : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

/--
If `a` and `b` are `Ordering`, then `a.then b` returns `a` unless it is `.eq`, in which case it
returns `b`. Additionally, it has “short-circuiting” behavior similar to boolean `&&`: if `a` is not
`.eq` then the expression for `b` is not evaluated.

This is a useful primitive for constructing lexicographic comparator functions. The `deriving Ord`
syntax on a structure uses the `Ord` instance to compare each field in order, combining the results
equivalently to `Ordering.then`.

Use `compareLex` to lexicographically combine two comparison functions.

Examples:
```lean example
structure Person where
  name : String
  age : Nat

-- Sort people first by name (in ascending order), and people with the same name by age (in
-- descending order)
instance : Ord Person where
  compare a b := (compare a.name b.name).then (compare b.age a.age)
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Dana", 50⟩
```
```output
Ordering.gt
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Gert", 50⟩
```
```output
Ordering.gt
```

```lean example
#eval Ord.compare (⟨"Gert", 33⟩ : Person) ⟨"Gert", 20⟩
```
```output
Ordering.lt
```
-/
@[macro_inline, expose] def «then» (a b : Ordering) : Ordering :=
  match a with
  | .eq => b
  | a => a

/-- Version of `Ordering.then'` for proof by reflection. -/
noncomputable def then' (a b : Ordering) : Ordering :=
  Ordering.rec a b a a

/--
Checks whether the ordering is `eq`.
-/
@[inline, expose]
def isEq : Ordering → Bool
  | eq => true
  | _ => false

/--
Checks whether the ordering is not `eq`.
-/
@[inline, expose]
def isNe : Ordering → Bool
  | eq => false
  | _ => true

/--
Checks whether the ordering is `lt` or `eq`.
-/
@[inline, expose]
def isLE : Ordering → Bool
  | gt => false
  | _ => true

/--
Checks whether the ordering is `lt`.
-/
@[inline, expose]
def isLT : Ordering → Bool
  | lt => true
  | _ => false

/--
Checks whether the ordering is `gt`.
-/
@[inline, expose]
def isGT : Ordering → Bool
  | gt => true
  | _ => false

/--
Checks whether the ordering is `gt` or `eq`.
-/
@[inline, expose]
def isGE : Ordering → Bool
  | lt => false
  | _ => true

section Lemmas

protected theorem «forall» {p : Ordering → Prop} : (∀ o, p o) ↔ p .lt ∧ p .eq ∧ p .gt := by
  constructor
  · intro h
    exact ⟨h _, h _, h _⟩
  · rintro ⟨h₁, h₂, h₃⟩ (_ | _ | _) <;> assumption

protected theorem «exists» {p : Ordering → Prop} : (∃ o, p o) ↔ p .lt ∨ p .eq ∨ p .gt := by
  constructor
  · rintro ⟨(_ | _ | _), h⟩
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr h)
  · rintro (h | h | h) <;> exact ⟨_, h⟩

instance [DecidablePred p] : Decidable (∀ o : Ordering, p o) :=
  decidable_of_decidable_of_iff Ordering.«forall».symm

instance [DecidablePred p] : Decidable (∃ o : Ordering, p o) :=
  decidable_of_decidable_of_iff Ordering.«exists».symm

@[simp] theorem isLT_lt : lt.isLT := rfl
@[simp] theorem isLE_lt : lt.isLE := rfl
@[simp] theorem isEq_lt : lt.isEq = false := rfl
@[simp] theorem isNe_lt : lt.isNe = true := rfl
@[simp] theorem isGE_lt : lt.isGE = false := rfl
@[simp] theorem isGT_lt : lt.isGT = false := rfl

@[simp] theorem isLT_eq : eq.isLT = false := rfl
@[simp] theorem isLE_eq : eq.isLE := rfl
@[simp] theorem isEq_eq : eq.isEq := rfl
@[simp] theorem isNe_eq : eq.isNe = false := rfl
@[simp] theorem isGE_eq : eq.isGE := rfl
@[simp] theorem isGT_eq : eq.isGT = false := rfl

@[simp] theorem isLT_gt : gt.isLT = false := rfl
@[simp] theorem isLE_gt : gt.isLE = false := rfl
@[simp] theorem isEq_gt : gt.isEq = false := rfl
@[simp] theorem isNe_gt : gt.isNe = true := rfl
@[simp] theorem isGE_gt : gt.isGE := rfl
@[simp] theorem isGT_gt : gt.isGT := rfl

@[simp] theorem lt_beq_eq : (lt == eq) = false := rfl
@[simp] theorem lt_beq_gt : (lt == gt) = false := rfl
@[simp] theorem eq_beq_lt : (eq == lt) = false := rfl
@[simp] theorem eq_beq_gt : (eq == gt) = false := rfl
@[simp] theorem gt_beq_lt : (gt == lt) = false := rfl
@[simp] theorem gt_beq_eq : (gt == eq) = false := rfl

@[simp] theorem swap_lt : lt.swap = .gt := rfl
@[simp] theorem swap_eq : eq.swap = .eq := rfl
@[simp] theorem swap_gt : gt.swap = .lt := rfl

theorem eq_eq_of_isLE_of_isLE_swap : ∀ {o : Ordering}, o.isLE → o.swap.isLE → o = .eq := by decide
theorem eq_eq_of_isGE_of_isGE_swap : ∀ {o : Ordering}, o.isGE → o.swap.isGE → o = .eq := by decide
theorem eq_eq_of_isLE_of_isGE : ∀ {o : Ordering}, o.isLE → o.isGE → o = .eq := by decide
theorem eq_swap_iff_eq_eq : ∀ {o : Ordering}, o = o.swap ↔ o = .eq := by decide
theorem eq_eq_of_eq_swap : ∀ {o : Ordering}, o = o.swap → o = .eq := eq_swap_iff_eq_eq.mp

@[simp] theorem isLE_eq_false : ∀ {o : Ordering}, o.isLE = false ↔ o = .gt := by decide
@[simp] theorem isGE_eq_false : ∀ {o : Ordering}, o.isGE = false ↔ o = .lt := by decide
@[simp] theorem isNe_eq_false : ∀ {o : Ordering}, o.isNe = false ↔ o = .eq := by decide
@[simp] theorem isEq_eq_false : ∀ {o : Ordering}, o.isEq = false ↔ ¬o = .eq := by decide

@[simp] theorem swap_eq_gt : ∀ {o : Ordering}, o.swap = .gt ↔ o = .lt := by decide
@[simp] theorem swap_eq_lt : ∀ {o : Ordering}, o.swap = .lt ↔ o = .gt := by decide
@[simp] theorem swap_eq_eq : ∀ {o : Ordering}, o.swap = .eq ↔ o = .eq := by decide

@[simp] theorem isLT_swap : ∀ {o : Ordering}, o.swap.isLT = o.isGT := by decide
@[simp] theorem isLE_swap : ∀ {o : Ordering}, o.swap.isLE = o.isGE := by decide
@[simp] theorem isEq_swap : ∀ {o : Ordering}, o.swap.isEq = o.isEq := by decide
@[simp] theorem isNe_swap : ∀ {o : Ordering}, o.swap.isNe = o.isNe := by decide
@[simp] theorem isGE_swap : ∀ {o : Ordering}, o.swap.isGE = o.isLE := by decide
@[simp] theorem isGT_swap : ∀ {o : Ordering}, o.swap.isGT = o.isLT := by decide

theorem isLE_of_eq_lt : ∀ {o : Ordering}, o = .lt → o.isLE := by decide
theorem isLE_of_eq_eq : ∀ {o : Ordering}, o = .eq → o.isLE := by decide
theorem isGE_of_eq_gt : ∀ {o : Ordering}, o = .gt → o.isGE := by decide
theorem isGE_of_eq_eq : ∀ {o : Ordering}, o = .eq → o.isGE := by decide

theorem ne_eq_of_eq_lt : ∀ {o : Ordering}, o = .lt → o ≠ .eq := by decide
theorem ne_eq_of_eq_gt : ∀ {o : Ordering}, o = .gt → o ≠ .eq := by decide

@[simp] theorem isLT_iff_eq_lt : ∀ {o : Ordering}, o.isLT ↔ o = .lt := by decide
@[simp] theorem isGT_iff_eq_gt : ∀ {o : Ordering}, o.isGT ↔ o = .gt := by decide
@[simp] theorem isEq_iff_eq_eq : ∀ {o : Ordering}, o.isEq ↔ o = .eq := by decide
@[simp] theorem isNe_iff_ne_eq : ∀ {o : Ordering}, o.isNe ↔ ¬o = .eq := by decide

theorem isLE_iff_ne_gt : ∀ {o : Ordering}, o.isLE ↔ ¬o = .gt := by decide
theorem isGE_iff_ne_lt : ∀ {o : Ordering}, o.isGE ↔ ¬o = .lt := by decide
theorem isLE_iff_eq_lt_or_eq_eq : ∀ {o : Ordering}, o.isLE ↔ o = .lt ∨ o = .eq := by decide
theorem isGE_iff_eq_gt_or_eq_eq : ∀ {o : Ordering}, o.isGE ↔ o = .gt ∨ o = .eq := by decide

theorem isLT_eq_beq_lt : ∀ {o : Ordering}, o.isLT = (o == .lt) := by decide
theorem isLE_eq_not_beq_gt : ∀ {o : Ordering}, o.isLE = (!o == .gt) := by decide
theorem isLE_eq_isLT_or_isEq : ∀ {o : Ordering}, o.isLE = (o.isLT || o.isEq) := by decide
theorem isGT_eq_beq_gt : ∀ {o : Ordering}, o.isGT = (o == .gt) := by decide
theorem isGE_eq_not_beq_lt : ∀ {o : Ordering}, o.isGE = (!o == .lt) := by decide
theorem isGE_eq_isGT_or_isEq : ∀ {o : Ordering}, o.isGE = (o.isGT || o.isEq) := by decide
theorem isEq_eq_beq_eq : ∀ {o : Ordering}, o.isEq = (o == .eq) := by decide
theorem isNe_eq_not_beq_eq : ∀ {o : Ordering}, o.isNe = (!o == .eq) := by decide
theorem isNe_eq_isLT_or_isGT : ∀ {o : Ordering}, o.isNe = (o.isLT || o.isGT) := by decide

@[simp] theorem not_isLT_eq_isGE : ∀ {o : Ordering}, (!o.isLT) = o.isGE := by decide
@[simp] theorem not_isLE_eq_isGT : ∀ {o : Ordering}, (!o.isLE) = o.isGT := by decide
@[simp] theorem not_isGT_eq_isLE : ∀ {o : Ordering}, (!o.isGT) = o.isLE := by decide
@[simp] theorem not_isGE_eq_isLT : ∀ {o : Ordering}, (!o.isGE) = o.isLT := by decide
@[simp] theorem not_isNe_eq_isEq : ∀ {o : Ordering}, (!o.isNe) = o.isEq := by decide
theorem not_isEq_eq_isNe : ∀ {o : Ordering}, (!o.isEq) = o.isNe := by decide

theorem ne_lt_iff_isGE : ∀ {o : Ordering}, ¬o = .lt ↔ o.isGE := by decide
theorem ne_gt_iff_isLE : ∀ {o : Ordering}, ¬o = .gt ↔ o.isLE := by decide

@[simp] theorem swap_swap : ∀ {o : Ordering}, o.swap.swap = o := by decide
@[simp] theorem swap_inj : ∀ {o₁ o₂ : Ordering}, o₁.swap = o₂.swap ↔ o₁ = o₂ := by decide

theorem swap_then : ∀ (o₁ o₂ : Ordering), (o₁.then o₂).swap = o₁.swap.then o₂.swap := by decide

theorem then_eq_lt : ∀ {o₁ o₂ : Ordering}, o₁.then o₂ = lt ↔ o₁ = lt ∨ o₁ = eq ∧ o₂ = lt := by decide
theorem then_eq_gt : ∀ {o₁ o₂ : Ordering}, o₁.then o₂ = gt ↔ o₁ = gt ∨ o₁ = eq ∧ o₂ = gt := by decide
@[simp] theorem then_eq_eq : ∀ {o₁ o₂ : Ordering}, o₁.then o₂ = eq ↔ o₁ = eq ∧ o₂ = eq := by decide

theorem isLT_then : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isLT = (o₁.isLT || o₁.isEq && o₂.isLT) := by decide
theorem isEq_then : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isEq = (o₁.isEq && o₂.isEq) := by decide
theorem isNe_then : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isNe = (o₁.isNe || o₂.isNe) := by decide
theorem isGT_then : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isGT = (o₁.isGT || o₁.isEq && o₂.isGT) := by decide

@[simp] theorem lt_then {o : Ordering} : lt.then o = lt := rfl
@[simp] theorem gt_then {o : Ordering} : gt.then o = gt := rfl
@[simp] theorem eq_then {o : Ordering} : eq.then o = o := rfl

@[simp] theorem then_eq : ∀ {o : Ordering}, o.then eq = o := by decide
@[simp] theorem then_self : ∀ {o : Ordering}, o.then o = o := by decide
theorem then_assoc : ∀ (o₁ o₂ o₃ : Ordering), (o₁.then o₂).then o₃ = o₁.then (o₂.then o₃) := by decide

theorem isLE_then_iff_or : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isLE ↔ o₁ = lt ∨ (o₁ = eq ∧ o₂.isLE) := by decide
theorem isLE_then_iff_and : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isLE ↔ o₁.isLE ∧ (o₁ = lt ∨ o₂.isLE) := by decide
theorem isLE_left_of_isLE_then : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isLE → o₁.isLE := by decide
theorem isGE_left_of_isGE_then : ∀ {o₁ o₂ : Ordering}, (o₁.then o₂).isGE → o₁.isGE := by decide

instance : Std.Associative Ordering.then := ⟨then_assoc⟩
instance : Std.IdempotentOp Ordering.then := ⟨fun _ => then_self⟩

instance : Std.LawfulIdentity Ordering.then eq where
  left_id _ := eq_then
  right_id _ := then_eq

theorem then'_eq_then (a b : Ordering) : a.then' b = a.then b := by
  cases a <;> simp [Ordering.then', Ordering.then]

end Lemmas

end Ordering

/--
Uses decidable less-than and equality relations to find an `Ordering`.

In particular, if `x < y` then the result is `Ordering.lt`. If `x = y` then the result is
`Ordering.eq`. Otherwise, it is `Ordering.gt`.

`compareOfLessAndBEq` uses `BEq` instead of `DecidableEq`.
-/
@[inline, expose] def compareOfLessAndEq {α} (x y : α) [LT α] [Decidable (x < y)] [DecidableEq α] : Ordering :=
  if x < y then Ordering.lt
  else if x = y then Ordering.eq
  else Ordering.gt

/--
Uses a decidable less-than relation and Boolean equality to find an `Ordering`.

In particular, if `x < y` then the result is `Ordering.lt`. If `x == y` then the result is
`Ordering.eq`. Otherwise, it is `Ordering.gt`.

`compareOfLessAndEq` uses `DecidableEq` instead of `BEq`.
-/
@[inline] def compareOfLessAndBEq {α} (x y : α) [LT α] [Decidable (x < y)] [BEq α] : Ordering :=
  if x < y then .lt
  else if x == y then .eq
  else .gt

/--
Compares `a` and `b` lexicographically by `cmp₁` and `cmp₂`.

`a` and `b` are first compared by `cmp₁`. If this returns `Ordering.eq`, `a` and `b` are compared
by `cmp₂` to break the tie.

To lexicographically combine two `Ordering`s, use `Ordering.then`.
-/
@[inline, expose] def compareLex (cmp₁ cmp₂ : α → β → Ordering) (a : α) (b : β) : Ordering :=
  (cmp₁ a b).then (cmp₂ a b)

section Lemmas

@[simp]
theorem compareLex_eq_eq {α} {cmp₁ cmp₂} {a b : α} :
    compareLex cmp₁ cmp₂ a b = .eq ↔ cmp₁ a b = .eq ∧ cmp₂ a b = .eq := by
  simp [compareLex]

theorem compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne {α : Type u} [LT α] [DecidableLT α] [DecidableEq α]
    (h : ∀ x y : α, x < y ↔ ¬ y < x ∧ x ≠ y) {x y : α} :
    compareOfLessAndEq x y = (compareOfLessAndEq y x).swap := by
  simp only [compareOfLessAndEq]
  split
  · rename_i h'
    rw [h] at h'
    simp only [h'.1, h'.2.symm, ↓reduceIte, Ordering.swap_gt]
  · split
    · rename_i h'
      have : ¬ y < y := Not.imp (·.2 rfl) <| (h y y).mp
      simp only [h', this, ↓reduceIte, Ordering.swap_eq]
    · rename_i h' h''
      replace h' := (h y x).mpr ⟨h', Ne.symm h''⟩
      simp only [h', ↓reduceIte, Ordering.swap_lt]

theorem lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (total : ∀ (x y : α), x ≤ y ∨ y ≤ x) (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) (x y : α) :
    x < y ↔ ¬ y < x ∧ x ≠ y := by
  simp only [← not_le, Classical.not_not]
  constructor
  · intro h
    have refl := by cases total y y <;> assumption
    exact ⟨(total _ _).resolve_left h, fun h' => (h' ▸ h) refl⟩
  · intro ⟨h₁, h₂⟩ h₃
    exact h₂ (antisymm h₁ h₃)

theorem compareOfLessAndEq_eq_swap
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (total : ∀ (x y : α), x ≤ y ∨ y ≤ x) (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) {x y : α} :
    compareOfLessAndEq x y = (compareOfLessAndEq y x).swap := by
  apply compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne
  exact lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le antisymm total not_le

@[simp]
theorem compareOfLessAndEq_eq_lt
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α] {x y : α} :
    compareOfLessAndEq x y = .lt ↔ x < y := by
  rw [compareOfLessAndEq]
  repeat' split <;> simp_all

theorem compareOfLessAndEq_eq_eq
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableLE α] [DecidableEq α]
    (refl : ∀ (x : α), x ≤ x) (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) {x y : α} :
    compareOfLessAndEq x y = .eq ↔ x = y := by
  rw [compareOfLessAndEq]
  repeat' split <;> try (simp_all; done)
  simp only [reduceCtorEq, false_iff]
  rintro rfl
  rename_i hlt
  simp [← not_le] at hlt
  exact hlt (refl x)

theorem compareOfLessAndEq_eq_gt_of_lt_iff_not_gt_and_ne
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α] {x y : α}
    (h : ∀ x y : α, x < y ↔ ¬ y < x ∧ x ≠ y) :
    compareOfLessAndEq x y = .gt ↔ y < x := by
  rw [compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne h, Ordering.swap_eq_gt]
  exact compareOfLessAndEq_eq_lt

theorem compareOfLessAndEq_eq_gt
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (total : ∀ (x y : α), x ≤ y ∨ y ≤ x) (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) (x y : α) :
    compareOfLessAndEq x y = .gt ↔ y < x := by
  apply compareOfLessAndEq_eq_gt_of_lt_iff_not_gt_and_ne
  exact lt_iff_not_gt_and_ne_of_antisymm_of_total_of_not_le antisymm total not_le

theorem isLE_compareOfLessAndEq
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableLE α] [DecidableEq α]
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) (total : ∀ (x y : α), x ≤ y ∨ y ≤ x) {x y : α} :
    (compareOfLessAndEq x y).isLE ↔ x ≤ y := by
  have refl (a : α) := by cases total a a <;> assumption
  rw [Ordering.isLE_iff_eq_lt_or_eq_eq, compareOfLessAndEq_eq_lt,
    compareOfLessAndEq_eq_eq refl not_le]
  constructor
  · rintro (h | rfl)
    · rw [← not_le] at h
      exact total _ _ |>.resolve_left h
    · exact refl x
  · intro hle
    by_cases hge : x ≥ y
    · exact Or.inr <| antisymm hle hge
    · exact Or.inl <| not_le.mp hge

end Lemmas

/--
`Ord α` provides a computable total order on `α`, in terms of the
`compare : α → α → Ordering` function.

Typically instances will be transitive, reflexive, and antisymmetric,
but this is not enforced by the typeclass.

There is a derive handler, so appending `deriving Ord` to an inductive type or structure
will attempt to create an `Ord` instance.
-/
@[ext]
class Ord (α : Type u) where
  /-- Compare two elements in `α` using the comparator contained in an `[Ord α]` instance. -/
  compare : α → α → Ordering

export Ord (compare)

/--
Compares two values by comparing the results of applying a function.

In particular, `x` is compared to `y` by comparing `f x` and `f y`.

Examples:
 * `compareOn (·.length) "apple" "banana" = .lt`
 * `compareOn (· % 3) 5 6 = .gt`
 * `compareOn (·.foldl max 0) [1, 2, 3] [3, 2, 1] = .eq`
-/
@[inline, expose] def compareOn [ord : Ord β] (f : α → β) (x y : α) : Ordering :=
  compare (f x) (f y)

instance : Ord Nat where
  compare x y := compareOfLessAndEq x y

instance : Ord Int where
  compare x y := compareOfLessAndEq x y

instance : Ord Bool where
  compare
  | false, true => Ordering.lt
  | true, false => Ordering.gt
  | _, _ => Ordering.eq

instance : Ord String where
  compare x y := compareOfLessAndEq x y

instance (n : Nat) : Ord (Fin n) where
  compare x y := compare x.val y.val

instance : Ord UInt8 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt16 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt32 where
  compare x y := compareOfLessAndEq x y

instance : Ord UInt64 where
  compare x y := compareOfLessAndEq x y

instance : Ord USize where
  compare x y := compareOfLessAndEq x y

instance : Ord Char where
  compare x y := compareOfLessAndEq x y

instance : Ord Int8 where
  compare x y := compareOfLessAndEq x y

instance : Ord Int16 where
  compare x y := compareOfLessAndEq x y

instance : Ord Int32 where
  compare x y := compareOfLessAndEq x y

instance : Ord Int64 where
  compare x y := compareOfLessAndEq x y

instance : Ord ISize where
  compare x y := compareOfLessAndEq x y

instance {n} : Ord (BitVec n) where
  compare x y := compareOfLessAndEq x y

instance [Ord α] : Ord (Option α) where
  compare
  | none,   none   => .eq
  | none,   some _ => .lt
  | some _, none   => .gt
  | some x, some y => compare x y

instance : Ord Ordering where
  compare := compareOn (·.toCtorIdx)

namespace List

@[specialize, expose]
protected def compareLex {α} (cmp : α → α → Ordering) :
    List α → List α → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | x :: xs, y :: ys => match cmp x y with
    | .lt => .lt
    | .eq => xs.compareLex cmp ys
    | .gt => .gt

instance {α} [Ord α] : Ord (List α) where
  compare := List.compareLex compare

protected theorem compare_eq_compareLex {α} [Ord α] :
    compare (α := List α) = List.compareLex compare := rfl

protected theorem compareLex_cons_cons {α} {cmp} {x y : α} {xs ys : List α} :
    (x :: xs).compareLex cmp (y :: ys) = (cmp x y).then (xs.compareLex cmp ys) := by
  rw [List.compareLex]
  split <;> simp_all

@[simp]
protected theorem compare_cons_cons {α} [Ord α] {x y : α} {xs ys : List α} :
    compare (x :: xs) (y :: ys) = (compare x y).then (compare xs ys) :=
  List.compareLex_cons_cons

protected theorem compareLex_nil_cons {α} {cmp} {x : α} {xs : List α} :
    [].compareLex cmp (x :: xs) = .lt :=
  rfl

@[simp]
protected theorem compare_nil_cons {α} [Ord α] {x : α} {xs : List α} :
    compare [] (x :: xs) = .lt :=
  rfl

protected theorem compareLex_cons_nil {α} {cmp} {x : α} {xs : List α} :
    (x :: xs).compareLex cmp [] = .gt :=
  rfl

@[simp]
protected theorem compare_cons_nil {α} [Ord α] {x : α} {xs : List α} :
    compare (x :: xs) [] = .gt :=
  rfl

protected theorem compareLex_nil_nil {α} {cmp} :
    [].compareLex (α := α) cmp [] = .eq :=
  rfl

@[simp]
protected theorem compare_nil_nil {α} [Ord α] :
    compare (α := List α) [] [] = .eq :=
  rfl

protected theorem isLE_compareLex_nil_left {α} {cmp} {xs : List α} :
    (List.compareLex (cmp := cmp) [] xs).isLE := by
  cases xs <;> simp [List.compareLex_nil_nil, List.compareLex_nil_cons]

protected theorem isLE_compare_nil_left {α} [Ord α] {xs : List α} :
    (compare [] xs).isLE :=
  List.isLE_compareLex_nil_left

protected theorem isLE_compareLex_nil_right {α} {cmp} {xs : List α} :
    (List.compareLex (cmp := cmp) xs []).isLE ↔ xs = [] := by
  cases xs <;> simp [List.compareLex_nil_nil, List.compareLex_cons_nil]

@[simp]
protected theorem isLE_compare_nil_right {α} [Ord α] {xs : List α} :
    (compare xs []).isLE ↔ xs = [] :=
  List.isLE_compareLex_nil_right

protected theorem isGE_compareLex_nil_left {α} {cmp} {xs : List α} :
    (List.compareLex (cmp := cmp) [] xs).isGE ↔ xs = [] := by
  cases xs <;> simp [List.compareLex_nil_nil, List.compareLex_nil_cons]

@[simp]
protected theorem isGE_compare_nil_left {α} [Ord α] {xs : List α} :
    (compare [] xs).isGE ↔ xs = [] :=
  List.isGE_compareLex_nil_left

protected theorem isGE_compareLex_nil_right {α} {cmp} {xs : List α} :
    (List.compareLex (cmp := cmp) xs []).isGE := by
  cases xs <;> simp [List.compareLex_nil_nil, List.compareLex_cons_nil]

protected theorem isGE_compare_nil_right {α} [Ord α] {xs : List α} :
    (compare xs []).isGE :=
  List.isGE_compareLex_nil_right

protected theorem compareLex_nil_left_eq_eq {α} {cmp} {xs : List α} :
    List.compareLex cmp [] xs = .eq ↔ xs = [] := by
  cases xs <;> simp [List.compareLex_nil_nil, List.compareLex_nil_cons]

@[simp]
protected theorem compare_nil_left_eq_eq {α} [Ord α] {xs : List α} :
    compare [] xs = .eq ↔ xs = [] :=
  List.compareLex_nil_left_eq_eq

protected theorem compareLex_nil_right_eq_eq {α} {cmp} {xs : List α} :
    xs.compareLex cmp [] = .eq ↔ xs = [] := by
  cases xs <;> simp [List.compareLex_nil_nil, List.compareLex_cons_nil]

@[simp]
protected theorem compare_nil_right_eq_eq {α} [Ord α] {xs : List α} :
    compare xs [] = .eq ↔ xs = [] :=
  List.compareLex_nil_right_eq_eq

end List

namespace Array

@[specialize]
protected def compareLex {α} (cmp : α → α → Ordering) (a₁ a₂ : Array α) : Ordering :=
  go 0
where go i :=
  if h₁ : a₁.size <= i then
    if a₂.size <= i then .eq else .lt
  else
    if h₂ : a₂.size <= i then
      .gt
    else match cmp a₁[i] a₂[i] with
      | .lt => .lt
      | .eq => go (i + 1)
      | .gt => .gt
termination_by a₁.size - i

instance {α} [Ord α] : Ord (Array α) where
  compare := Array.compareLex compare

protected theorem compare_eq_compareLex {α} [Ord α] :
    compare (α := Array α) = Array.compareLex compare := rfl

private theorem compareLex.go_succ {α} {cmp} {x₁ x₂} {a₁ a₂ : List α} {i} :
    compareLex.go cmp (x₁ :: a₁).toArray (x₂ :: a₂).toArray (i + 1) =
      compareLex.go cmp a₁.toArray a₂.toArray i := by
  induction i using Array.compareLex.go.induct cmp a₁.toArray a₂.toArray
  all_goals try
    conv => congr <;> rw [compareLex.go]
    simp
    repeat' split <;> (try simp_all; done)

protected theorem _root_.List.compareLex_eq_compareLex_toArray {α} {cmp} {l₁ l₂ : List α} :
    List.compareLex cmp l₁ l₂ = Array.compareLex cmp l₁.toArray l₂.toArray := by
  simp only [Array.compareLex]
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂
    · simp [Array.compareLex.go, List.compareLex_nil_nil]
    · simp [Array.compareLex.go, List.compareLex_nil_cons]
  | cons x xs ih =>
    cases l₂
    · simp [Array.compareLex.go, List.compareLex_cons_nil]
    · rw [Array.compareLex.go, List.compareLex_cons_cons]
      simp only [List.size_toArray, List.length_cons, Nat.le_zero_eq, Nat.add_one_ne_zero,
        ↓reduceDIte, List.getElem_toArray, List.getElem_cons_zero, Nat.zero_add]
      split <;> simp_all [compareLex.go_succ]

protected theorem _root_.List.compare_eq_compare_toArray {α} [Ord α] {l₁ l₂ : List α} :
    compare l₁ l₂ = compare l₁.toArray l₂.toArray :=
  List.compareLex_eq_compareLex_toArray

protected theorem compareLex_eq_compareLex_toList {α} {cmp} {a₁ a₂ : Array α} :
    Array.compareLex cmp a₁ a₂ = List.compareLex cmp a₁.toList a₂.toList := by
  rw [List.compareLex_eq_compareLex_toArray]

protected theorem compare_eq_compare_toList {α} [Ord α] {a₁ a₂ : Array α} :
    compare a₁ a₂ = compare a₁.toList a₂.toList :=
  Array.compareLex_eq_compareLex_toList

end Array

namespace Vector

@[expose]
protected def compareLex {α n} (cmp : α → α → Ordering) (a b : Vector α n) : Ordering :=
  Array.compareLex cmp a.toArray b.toArray

instance {α n} [Ord α] : Ord (Vector α n) where
  compare := Vector.compareLex compare

protected theorem compareLex_eq_compareLex_toArray {α n cmp} {a b : Vector α n} :
    Vector.compareLex cmp a b = Array.compareLex cmp a.toArray b.toArray :=
  rfl

protected theorem compareLex_eq_compareLex_toList {α n cmp} {a b : Vector α n} :
    Vector.compareLex cmp a b = List.compareLex cmp a.toList b.toList :=
  Array.compareLex_eq_compareLex_toList

protected theorem compare_eq_compare_toArray {α n} [Ord α] {a b : Vector α n} :
    compare a b = compare a.toArray b.toArray :=
  rfl

protected theorem compare_eq_compare_toList {α n} [Ord α] {a b : Vector α n} :
    compare a b = compare a.toList b.toList :=
  Array.compare_eq_compare_toList

end Vector

/-- The lexicographic order on pairs. -/
@[expose] def lexOrd [Ord α] [Ord β] : Ord (α × β) where
  compare := compareLex (compareOn (·.1)) (compareOn (·.2))

/--
Constructs an `BEq` instance from an `Ord` instance that asserts that the result of `compare` is
`Ordering.eq`.
-/
@[expose] def beqOfOrd [Ord α] : BEq α where
  beq a b := (compare a b).isEq

/--
Constructs an `LT` instance from an `Ord` instance that asserts that the result of `compare` is
`Ordering.lt`.
-/
@[expose] def ltOfOrd [Ord α] : LT α where
  lt a b := compare a b = Ordering.lt

@[inline]
instance [Ord α] : DecidableRel (@LT.lt α ltOfOrd) := fun a b =>
  decidable_of_bool (compare a b).isLT Ordering.isLT_iff_eq_lt

/--
Constructs an `LT` instance from an `Ord` instance that asserts that the result of `compare`
satisfies `Ordering.isLE`.
-/
@[expose] def leOfOrd [Ord α] : LE α where
  le a b := (compare a b).isLE

@[inline]
instance [Ord α] : DecidableRel (@LE.le α leOfOrd) := fun _ _ => instDecidableEqBool ..

namespace Ord

/--
Constructs a `BEq` instance from an `Ord` instance.
-/
@[expose] protected abbrev toBEq (ord : Ord α) : BEq α :=
  beqOfOrd

/--
Constructs an `LT` instance from an `Ord` instance.
-/
@[expose] protected abbrev toLT (ord : Ord α) : LT α :=
  ltOfOrd

/--
Constructs an `LE` instance from an `Ord` instance.
-/
@[expose] protected abbrev toLE (ord : Ord α) : LE α :=
  leOfOrd

/--
Inverts the order of an `Ord` instance.

The result is an `Ord α` instance that returns `Ordering.lt` when `ord` would return `Ordering.gt`
and that returns `Ordering.gt` when `ord` would return `Ordering.lt`.
-/
@[expose] protected def opposite (ord : Ord α) : Ord α where
  compare x y := ord.compare y x

/--
Constructs an `Ord` instance that compares values according to the results of `f`.

In particular, `ord.on f` compares `x` and `y` by comparing `f x` and `f y` according to `ord`.

The function `compareOn` can be used to perform this comparison without constructing an intermediate
`Ord` instance.
-/
@[expose] protected def on (_ : Ord β) (f : α → β) : Ord α where
  compare := compareOn f

/--
Constructs the lexicographic order on products `α × β` from orders for `α` and `β`.
-/
@[expose] protected abbrev lex (_ : Ord α) (_ : Ord β) : Ord (α × β) :=
  lexOrd

/--
Constructs an `Ord` instance from two existing instances by combining them lexicographically.

The resulting instance compares elements first by `ord₁` and then, if this returns `Ordering.eq`, by
`ord₂`.

The function `compareLex` can be used to perform this comparison without constructing an
intermediate `Ord` instance. `Ordering.then` can be used to lexicographically combine the results of
comparisons.
-/
@[expose] protected def lex' (ord₁ ord₂ : Ord α) : Ord α where
  compare := compareLex ord₁.compare ord₂.compare

end Ord
