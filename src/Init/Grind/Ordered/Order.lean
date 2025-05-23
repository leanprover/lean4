/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.Order

namespace Lean.Grind

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

namespace Preorder

variable {α : Type u} [Preorder α]

theorem le_of_lt {a b : α} (h : a < b) : a ≤ b := (lt_iff_le_not_le.mp h).1

theorem lt_of_lt_of_le {a b c : α} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  simp [lt_iff_le_not_le] at h₁ ⊢
  exact ⟨le_trans h₁.1 h₂, fun h => h₁.2 (le_trans h₂ h)⟩

theorem lt_of_le_of_lt {a b c : α} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  simp [lt_iff_le_not_le] at h₂ ⊢
  exact ⟨le_trans h₁ h₂.1, fun h => h₂.2 (le_trans h h₁)⟩

theorem lt_trans {a b c : α} (h₁ : a < b) (h₂ : b < c) : a < c :=
  lt_of_lt_of_le h₁ (le_of_lt h₂)

theorem lt_irrefl (a : α) : ¬ (a < a) := by
  intro h
  simp [lt_iff_le_not_le] at h

theorem ne_of_lt {a b : α} (h : a < b) : a ≠ b :=
  fun w => lt_irrefl a (w.symm ▸ h)

theorem ne_of_gt {a b : α} (h : a > b) : a ≠ b :=
  fun w => lt_irrefl b (w.symm ▸ h)

theorem not_ge_of_lt {a b : α} (h : a < b) : ¬b ≤ a :=
  fun w => lt_irrefl a (lt_of_lt_of_le h w)

theorem not_gt_of_lt {a b : α} (h : a < b) : ¬a > b :=
  fun w => lt_irrefl a (lt_trans h w)

end Preorder

class PartialOrder (α : Type u) extends Preorder α where
  le_antisymm : ∀ {a b : α}, a ≤ b → b ≤ a → a = b

namespace PartialOrder

variable {α : Type u} [PartialOrder α]

theorem le_iff_lt_or_eq {a b : α} : a ≤ b ↔ a < b ∨ a = b := by
  constructor
  · intro h
    rw [Preorder.lt_iff_le_not_le, Classical.or_iff_not_imp_right]
    exact fun w => ⟨h, fun w' => w (le_antisymm h w')⟩
  · intro h
    cases h with
    | inl h => exact Preorder.le_of_lt h
    | inr h => subst h; exact Preorder.le_refl a

end PartialOrder

class LinearOrder (α : Type u) extends PartialOrder α where
  le_total : ∀ a b : α, a ≤ b ∨ b ≤ a

namespace LinearOrder

variable {α : Type u} [LinearOrder α]

theorem trichotomy (a b : α) : a < b ∨ a = b ∨ b < a := by
  cases LinearOrder.le_total a b with
  | inl h =>
    rw [PartialOrder.le_iff_lt_or_eq] at h
    cases h with
    | inl h => left; exact h
    | inr h => right; left; exact h
  | inr h =>
    rw [PartialOrder.le_iff_lt_or_eq] at h
    cases h with
    | inl h => right; right; exact h
    | inr h => right; left; exact h.symm

end LinearOrder

end Lean.Grind
