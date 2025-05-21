/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.CommRing.Basic
import Init.Grind.Ordered.Module

namespace Lean.Grind

class Ring.IsOrdered (R : Type u) [Ring R] [Preorder R] extends IntModule.IsOrdered R where
  /-- In a strict ordered semiring, we have `0 < 1`. -/
  zero_lt_one : 0 < 1
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the left
  by a positive element `0 < c` to obtain `c * a < c * b`. -/
  mul_lt_mul_of_pos_left : ∀ {a b c : R}, a < b → 0 < c → c * a < c * b
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the right
  by a positive element `0 < c` to obtain `a * c < b * c`. -/
  mul_lt_mul_of_pos_right : ∀ {a b c : R}, a < b → 0 < c → a * c < b * c

namespace Ring.IsOrdered

variable {R : Type u} [Ring R] [PartialOrder R] [Ring.IsOrdered R]

theorem mul_le_mul_of_nonneg_left {a b c : R} (h : a ≤ b) (h' : 0 ≤ c) : c * a ≤ c * b := by
  rw [PartialOrder.le_iff_lt_or_eq] at h'
  cases h' with
  | inl h' =>
    have p := mul_lt_mul_of_pos_left (a := a) (b := b) (c := c)
    rw [PartialOrder.le_iff_lt_or_eq] at h
    cases h with
    | inl h => exact Preorder.le_of_lt (p h h')
    | inr h => subst h; exact Preorder.le_refl (c * a)
  | inr h' => subst h'; simp [Semiring.zero_mul, Preorder.le_refl]

theorem mul_le_mul_of_nonneg_right {a b c : R} (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  rw [PartialOrder.le_iff_lt_or_eq] at h'
  cases h' with
  | inl h' =>
    have p := mul_lt_mul_of_pos_right (a := a) (b := b) (c := c)
    rw [PartialOrder.le_iff_lt_or_eq] at h
    cases h with
    | inl h => exact Preorder.le_of_lt (p h h')
    | inr h => subst h; exact Preorder.le_refl (a * c)
  | inr h' => subst h'; simp [Semiring.mul_zero, Preorder.le_refl]

theorem mul_nonneg {a b : R} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b := by
  simpa [Semiring.zero_mul] using mul_le_mul_of_nonneg_right h₁ h₂

theorem mul_pos {a b : R} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := by
  simpa [Semiring.zero_mul] using mul_lt_mul_of_pos_right h₁ h₂

theorem sq_nonneg {a : R} (h : 0 ≤ a) : 0 ≤ a^2 := by
  rw [Semiring.pow_two]
  apply mul_nonneg h h

theorem sq_pos {a : R} (h : 0 < a) : 0 < a^2 := by
  rw [Semiring.pow_two]
  apply mul_pos h h

end Ring.IsOrdered

end Lean.Grind
