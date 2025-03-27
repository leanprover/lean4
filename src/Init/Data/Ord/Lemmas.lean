/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Ord.Basic

/--
This file contains lemmas about `Ord`, `Ordering` and comparison functions.

Many useful properties about `Ord` instances are also available via the `OrientedOrd` and `TransOrd`
typeclasses and their instances defined in `Std.Classes.Ord`.
-/

@[simp]
theorem compareLex_eq_eq {α} {cmp₁ cmp₂} {a b : α} :
    compareLex cmp₁ cmp₂ a b = .eq ↔ cmp₁ a b = .eq ∧ cmp₂ a b = .eq := by
  simp [compareLex, Ordering.then_eq_eq]

theorem compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne {α : Type u} [LT α] [DecidableLT α] [DecidableEq α]
    (h : ∀ x y : α, x < y ↔ ¬ y < x ∧ x ≠ y) {x y : α} :
    compareOfLessAndEq x y = (compareOfLessAndEq y x).swap := by
  simp only [compareOfLessAndEq]
  split
  · rename_i h'
    rw [h] at h'
    simp only [h'.1, h'.2.symm, reduceIte, Ordering.swap_gt]
  · split
    · rename_i h'
      have : ¬y < y := Not.imp (·.2 rfl) <| (h y y).mp
      simp only [h', this, reduceIte, Ordering.swap_eq]
    · rename_i h' h''
      replace h' := (h y x).mpr ⟨h', Ne.symm h''⟩
      simp only [h', Ne.symm h'', reduceIte, Ordering.swap_lt]

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
    compareOfLessAndEq x y = .gt ↔ x > y := by
  rw [compareOfLessAndEq_eq_swap_of_lt_iff_not_gt_and_ne h, Ordering.swap_eq_gt]
  exact compareOfLessAndEq_eq_lt

theorem compareOfLessAndEq_eq_gt
    {α : Type u} [LT α] [LE α] [DecidableLT α] [DecidableEq α]
    (antisymm : ∀ {x y : α}, x ≤ y → y ≤ x → x = y)
    (total : ∀ (x y : α), x ≤ y ∨ y ≤ x) (not_le : ∀ {x y : α}, ¬ x ≤ y ↔ y < x) (x y : α) :
    compareOfLessAndEq x y = .gt ↔ x > y := by
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
