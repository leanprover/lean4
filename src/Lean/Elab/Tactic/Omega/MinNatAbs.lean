/-
Copyright (c) 2023 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.BinderPredicates
import Init.Data.Int.Order
import Init.Data.List.MinMax
import Init.Data.Nat.MinMax
import Init.Data.Option.Lemmas

/-!
# `List.nonzeroMinimum`, `List.minNatAbs`, `List.maxNatAbs`

`List.minNatAbs` computes the minimum non-zero absolute value of a `List Int`.
This is not generally useful outside of the implementation of the `omega` tactic,
so we keep it in the `Lean/Elab/Tactic/Omega` directory
(although the definitions are in the `List` namespace).

-/


namespace List

/--
The minimum non-zero entry in a list of natural numbers, or zero if all entries are zero.

We completely characterize the function via
`nonzeroMinimum_eq_zero_iff` and `nonzeroMinimum_eq_nonzero_iff` below.
-/
def nonzeroMinimum (xs : List Nat) : Nat := xs.filter (· ≠ 0) |>.min? |>.getD 0

-- A specialization of `minimum?_eq_some_iff` to Nat.
-- This is a duplicate `min?_eq_some_iff'` proved in `Init.Data.List.Nat.Basic`,
-- and could be deduplicated but the import hierarchy is awkward.
theorem min?_eq_some_iff'' {xs : List Nat} :
    xs.min? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, a ≤ b) :=
  min?_eq_some_iff
    (le_refl := Nat.le_refl)
    (min_eq_or := fun _ _ => Nat.min_def .. ▸ by split <;> simp)
    (le_min_iff := fun _ _ _ => Nat.le_min)

open Classical in
@[simp] theorem nonzeroMinimum_eq_zero_iff {xs : List Nat} :
    xs.nonzeroMinimum = 0 ↔ ∀ x ∈ xs, x = 0 := by
  simp [nonzeroMinimum, Option.getD_eq_iff, min?_eq_none_iff, min?_eq_some_iff'',
    filter_eq_nil_iff, mem_filter]

theorem nonzeroMinimum_mem {xs : List Nat} (w : xs.nonzeroMinimum ≠ 0) :
    xs.nonzeroMinimum ∈ xs := by
  dsimp [nonzeroMinimum] at *
  generalize h : (xs.filter (· ≠ 0) |>.min?) = m at *
  match m, w with
  | some (m+1), _ => simp_all [min?_eq_some_iff'', mem_filter]

theorem nonzeroMinimum_pos {xs : List Nat} (m : a ∈ xs) (h : a ≠ 0) : 0 < xs.nonzeroMinimum :=
  Nat.pos_iff_ne_zero.mpr fun w => h (nonzeroMinimum_eq_zero_iff.mp w _ m)

theorem nonzeroMinimum_le {xs : List Nat} (m : a ∈ xs) (h : a ≠ 0) : xs.nonzeroMinimum ≤ a := by
  have : (xs.filter (· ≠ 0) |>.min?) = some xs.nonzeroMinimum := by
    have w := nonzeroMinimum_pos m h
    dsimp [nonzeroMinimum] at *
    generalize h : (xs.filter (· ≠ 0) |>.min?) = m? at *
    match m?, w with
    | some m?, _ => rfl
  rw [min?_eq_some_iff''] at this
  apply this.2
  simp [List.mem_filter]
  exact ⟨m, h⟩

theorem nonzeroMinimum_eq_nonzero_iff {xs : List Nat} {y : Nat} (h : y ≠ 0) :
    xs.nonzeroMinimum = y ↔ y ∈ xs ∧ (∀ x ∈ xs, y ≤ x ∨ x = 0) := by
  constructor
  · rintro rfl
    constructor
    exact nonzeroMinimum_mem h
    intro y m
    by_cases w : y = 0
    · right; exact w
    · left; apply nonzeroMinimum_le m w
  · rintro ⟨m, w⟩
    apply Nat.le_antisymm
    · exact nonzeroMinimum_le m h
    · have nz : xs.nonzeroMinimum ≠ 0 := by
        apply Nat.pos_iff_ne_zero.mp
        apply nonzeroMinimum_pos m h
      specialize w (nonzeroMinimum xs) (nonzeroMinimum_mem nz)
      cases w with
      | inl h => exact h
      | inr h => exact False.elim (nz h)

theorem nonzeroMinimum_eq_of_nonzero {xs : List Nat} (h : xs.nonzeroMinimum ≠ 0) :
    ∃ x ∈ xs, xs.nonzeroMinimum = x :=
  ⟨xs.nonzeroMinimum, ((nonzeroMinimum_eq_nonzero_iff h).mp rfl).1, rfl⟩

theorem nonzeroMinimum_le_iff {xs : List Nat} {y : Nat} :
    xs.nonzeroMinimum ≤ y ↔ xs.nonzeroMinimum = 0 ∨ ∃ x ∈ xs, x ≤ y ∧ x ≠ 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [Classical.or_iff_not_imp_right]
    simp only [ne_eq, not_exists, not_and, Classical.not_not, nonzeroMinimum_eq_zero_iff]
    intro w
    apply nonzeroMinimum_eq_zero_iff.mp
    if p : xs.nonzeroMinimum = 0 then
      exact p
    else
      exact w _ (nonzeroMinimum_mem p) h
  · match h with
    | .inl h => simp [h]
    | .inr ⟨x, m, le, ne⟩ => exact Nat.le_trans (nonzeroMinimum_le m ne) le

theorem nonzeroMininum_map_le_nonzeroMinimum (f : α → β) (p : α → Nat) (q : β → Nat) (xs : List α)
    (h : ∀ a, a ∈ xs → (p a = 0 ↔ q (f a) = 0))
    (w : ∀ a, a ∈ xs → p a ≠ 0 → q (f a) ≤ p a) :
    ((xs.map f).map q).nonzeroMinimum ≤ (xs.map p).nonzeroMinimum := by
  rw [nonzeroMinimum_le_iff]
  if z : (xs.map p).nonzeroMinimum = 0 then
    rw [nonzeroMinimum_eq_zero_iff]
    simp_all
  else
    have := nonzeroMinimum_eq_of_nonzero z
    simp only [mem_map] at this
    obtain ⟨x, ⟨a, m, rfl⟩, eq⟩ := this
    refine .inr ⟨q (f a), List.mem_map_of_mem (List.mem_map_of_mem m), ?_, ?_⟩
    · rw [eq] at z ⊢
      apply w _ m z
    · rwa [Ne, ← h _ m, ← eq]

/--
The minimum absolute value of a nonzero entry, or zero if all entries are zero.

We completely characterize the function via
`minNatAbs_eq_zero_iff` and `minNatAbs_eq_nonzero_iff` below.
-/
def minNatAbs (xs : List Int) : Nat := xs.map Int.natAbs |>.nonzeroMinimum

@[simp] theorem minNatAbs_eq_zero_iff {xs : List Int} : xs.minNatAbs = 0 ↔ ∀ y ∈ xs, y = 0 := by
  simp [minNatAbs]

theorem minNatAbs_eq_nonzero_iff (xs : List Int) (w : z ≠ 0) :
    xs.minNatAbs = z ↔ (∃ y ∈ xs, y.natAbs = z) ∧ (∀ y ∈ xs, z ≤ y.natAbs ∨ y = 0) := by
  simp [minNatAbs, nonzeroMinimum_eq_nonzero_iff w]

@[simp] theorem minNatAbs_nil : ([] : List Int).minNatAbs = 0 := rfl

/-- The maximum absolute value in a list of integers. -/
def maxNatAbs (xs : List Int) : Nat := xs.map Int.natAbs |>.max? |>.getD 0
