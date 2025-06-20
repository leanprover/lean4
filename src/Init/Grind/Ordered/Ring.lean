/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Ring.Basic
import Init.Grind.Ordered.Module

namespace Lean.Grind

class Ring.IsOrdered (R : Type u) [Ring R] [Preorder R] extends IntModule.IsOrdered R where
  /-- In a strict ordered semiring, we have `0 < 1`. -/
  zero_lt_one : (0 : R) < 1
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the left
  by a positive element `0 < c` to obtain `c * a < c * b`. -/
  mul_lt_mul_of_pos_left : ∀ {a b c : R}, a < b → 0 < c → c * a < c * b
  /-- In a strict ordered semiring, we can multiply an inequality `a < b` on the right
  by a positive element `0 < c` to obtain `a * c < b * c`. -/
  mul_lt_mul_of_pos_right : ∀ {a b c : R}, a < b → 0 < c → a * c < b * c

namespace Ring.IsOrdered

variable {R : Type u} [Ring R]
section PartialOrder

variable [PartialOrder R] [Ring.IsOrdered R]

theorem zero_le_one : (0 : R) ≤ 1 := Preorder.le_of_lt zero_lt_one

theorem not_one_lt_zero : ¬ ((1 : R) < 0) :=
  fun h => Preorder.lt_irrefl (0 : R) (Preorder.lt_trans zero_lt_one h)

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

theorem mul_le_mul_of_nonpos_left {a b c : R} (h : a ≤ b) (h' : c ≤ 0) : c * b ≤ c * a := by
  have := mul_le_mul_of_nonneg_left h (IntModule.IsOrdered.neg_nonneg_iff.mpr h')
  rwa [Ring.neg_mul, Ring.neg_mul, IntModule.IsOrdered.neg_le_iff, IntModule.neg_neg] at this

theorem mul_le_mul_of_nonpos_right {a b c : R} (h : a ≤ b) (h' : c ≤ 0) : b * c ≤ a * c := by
  have := mul_le_mul_of_nonneg_right h (IntModule.IsOrdered.neg_nonneg_iff.mpr h')
  rwa [Ring.mul_neg, Ring.mul_neg, IntModule.IsOrdered.neg_le_iff, IntModule.neg_neg] at this

theorem mul_lt_mul_of_neg_left {a b c : R} (h : a < b) (h' : c < 0) : c * b < c * a := by
  have := mul_lt_mul_of_pos_left h (IntModule.IsOrdered.neg_pos_iff.mpr h')
  rwa [Ring.neg_mul, Ring.neg_mul, IntModule.IsOrdered.neg_lt_iff, IntModule.neg_neg] at this

theorem mul_lt_mul_of_neg_right {a b c : R} (h : a < b) (h' : c < 0) : b * c < a * c := by
  have := mul_lt_mul_of_pos_right h (IntModule.IsOrdered.neg_pos_iff.mpr h')
  rwa [Ring.mul_neg, Ring.mul_neg, IntModule.IsOrdered.neg_lt_iff, IntModule.neg_neg] at this

theorem mul_nonneg {a b : R} (h₁ : 0 ≤ a) (h₂ : 0 ≤ b) : 0 ≤ a * b := by
  simpa [Semiring.zero_mul] using mul_le_mul_of_nonneg_right h₁ h₂

theorem mul_nonneg_of_nonpos_of_nonpos {a b : R} (h₁ : a ≤ 0) (h₂ : b ≤ 0) : 0 ≤ a * b := by
  have := mul_nonneg (IntModule.IsOrdered.neg_nonneg_iff.mpr h₁) (IntModule.IsOrdered.neg_nonneg_iff.mpr h₂)
  simpa [Ring.neg_mul, Ring.mul_neg, Ring.neg_neg] using this

theorem mul_nonpos_of_nonneg_of_nonpos {a b : R} (h₁ : 0 ≤ a) (h₂ : b ≤ 0) : a * b ≤ 0 := by
  rw [← IntModule.IsOrdered.neg_nonneg_iff, ← Ring.mul_neg]
  apply mul_nonneg h₁ (IntModule.IsOrdered.neg_nonneg_iff.mpr h₂)

theorem mul_nonpos_of_nonpos_of_nonneg {a b : R} (h₁ : a ≤ 0) (h₂ : 0 ≤ b) : a * b ≤ 0 := by
  rw [← IntModule.IsOrdered.neg_nonneg_iff, ← Ring.neg_mul]
  apply mul_nonneg (IntModule.IsOrdered.neg_nonneg_iff.mpr h₁) h₂

theorem mul_pos {a b : R} (h₁ : 0 < a) (h₂ : 0 < b) : 0 < a * b := by
  simpa [Semiring.zero_mul] using mul_lt_mul_of_pos_right h₁ h₂

theorem mul_pos_of_neg_of_neg {a b : R} (h₁ : a < 0) (h₂ : b < 0) : 0 < a * b := by
  have := mul_pos (IntModule.IsOrdered.neg_pos_iff.mpr h₁) (IntModule.IsOrdered.neg_pos_iff.mpr h₂)
  simpa [Ring.neg_mul, Ring.mul_neg, Ring.neg_neg] using this

theorem mul_neg_of_pos_of_neg {a b : R} (h₁ : 0 < a) (h₂ : b < 0) : a * b < 0 := by
  rw [← IntModule.IsOrdered.neg_pos_iff, ← Ring.mul_neg]
  apply mul_pos h₁ (IntModule.IsOrdered.neg_pos_iff.mpr h₂)

theorem mul_neg_of_neg_of_pos {a b : R} (h₁ : a < 0) (h₂ : 0 < b) : a * b < 0 := by
  rw [← IntModule.IsOrdered.neg_pos_iff, ← Ring.neg_mul]
  apply mul_pos (IntModule.IsOrdered.neg_pos_iff.mpr h₁) h₂

end PartialOrder

section LinearOrder

variable [LinearOrder R] [Ring.IsOrdered R]

theorem mul_nonneg_iff {a b : R} : 0 ≤ a * b ↔ 0 ≤ a ∧ 0 ≤ b ∨ a ≤ 0 ∧ b ≤ 0 := by
  rcases LinearOrder.trichotomy 0 a with (ha | rfl | ha)
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, mul_nonneg]
    · simp [Semiring.mul_zero, Preorder.le_refl, LinearOrder.le_total]
    · have m : a * b < 0 := mul_neg_of_pos_of_neg ha hb
      simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, Preorder.not_ge_of_lt m,
        Preorder.not_ge_of_lt ha, Preorder.not_ge_of_lt hb]
  · simp [Semiring.zero_mul, Preorder.le_refl, LinearOrder.le_total]
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · have m : a * b < 0 := mul_neg_of_neg_of_pos ha hb
      simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, Preorder.not_ge_of_lt m,
        Preorder.not_ge_of_lt ha, Preorder.not_ge_of_lt hb]
    · simp [Semiring.mul_zero, Preorder.le_refl, LinearOrder.le_total]
    · simp [Preorder.le_of_lt ha, Preorder.le_of_lt hb, mul_nonneg_of_nonpos_of_nonpos]

theorem mul_pos_iff {a b : R} : 0 < a * b ↔ 0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases LinearOrder.trichotomy 0 a with (ha | rfl | ha)
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · simp [ha, hb, mul_pos]
    · simp [Preorder.lt_irrefl, Semiring.mul_zero]
    · have m : a * b < 0 := mul_neg_of_pos_of_neg ha hb
      simp [ha, hb, Preorder.not_gt_of_lt m,
        Preorder.not_gt_of_lt ha, Preorder.not_gt_of_lt hb]
  · simp [Preorder.lt_irrefl, Semiring.zero_mul]
  · rcases LinearOrder.trichotomy 0 b with (hb | rfl | hb)
    · have m : a * b < 0 := mul_neg_of_neg_of_pos ha hb
      simp [ha, hb, Preorder.not_gt_of_lt m,
        Preorder.not_gt_of_lt ha, Preorder.not_gt_of_lt hb]
    · simp [Preorder.lt_irrefl, Semiring.mul_zero]
    · simp [ha, hb, mul_pos_of_neg_of_neg]

theorem sq_nonneg {a : R} : 0 ≤ a^2 := by
  rw [Semiring.pow_two, mul_nonneg_iff]
  rcases LinearOrder.le_total 0 a with (h | h)
  · exact .inl ⟨h, h⟩
  · exact .inr ⟨h, h⟩

theorem sq_pos {a : R} (h : a ≠ 0) : 0 < a^2 := by
  rw [Semiring.pow_two, mul_pos_iff]
  rcases LinearOrder.trichotomy 0 a with (h' | rfl | h')
  · exact .inl ⟨h', h'⟩
  · simp at h
  · exact .inr ⟨h', h'⟩

end LinearOrder

end Ring.IsOrdered

end Lean.Grind
