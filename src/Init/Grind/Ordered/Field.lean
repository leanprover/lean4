/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Ring.Field
import Init.Grind.Ordered.Ring

namespace Lean.Grind

namespace Field.IsOrdered

variable {R : Type u} [Field R] [LinearOrder R] [OrderedRing R]

open OrderedAdd
open OrderedRing

theorem pos_of_inv_pos {a : R} (h : 0 < a⁻¹) : 0 < a := by
  rcases LinearOrder.trichotomy 0 a with (h' | rfl | h')
  · exact h'
  · simpa [Field.inv_zero] using h
  · exfalso
    have := OrderedRing.mul_neg_of_pos_of_neg h h'
    rw [inv_mul_cancel (Preorder.ne_of_lt h')] at this
    exact OrderedRing.not_one_lt_zero this

theorem inv_pos_iff {a : R} : 0 < a⁻¹ ↔ 0 < a := by
  constructor
  · exact pos_of_inv_pos
  · intro h
    rw [← Field.inv_inv a] at h
    exact pos_of_inv_pos h

theorem inv_neg_iff {a : R} : a⁻¹ < 0 ↔ a < 0 := by
  have := inv_pos_iff (a := -a)
  rw [Field.inv_neg] at this
  simpa [neg_pos_iff]

theorem inv_nonneg_iff {a : R} : 0 ≤ a⁻¹ ↔ 0 ≤ a := by
  simp [PartialOrder.le_iff_lt_or_eq, inv_pos_iff, Field.zero_eq_inv_iff]

theorem inv_nonpos_iff {a : R} : a⁻¹ ≤ 0 ↔ a ≤ 0 := by
  have := inv_nonneg_iff (a := -a)
  rw [Field.inv_neg] at this
  simpa [neg_nonneg_iff] using this

private theorem mul_le_of_le_mul_inv {a b c : R} (h : 0 < c) (h' : a ≤ b * c⁻¹) : a * c ≤ b := by
  simpa [Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_gt h), Semiring.mul_one] using
    OrderedRing.mul_le_mul_of_nonneg_right h' (Preorder.le_of_lt h)

private theorem le_mul_inv_of_mul_le {a b c : R} (h : 0 < b) (h' : a * b ≤ c) : a ≤ c * b⁻¹ := by
  simpa [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_gt h), Semiring.mul_one] using
    OrderedRing.mul_le_mul_of_nonneg_right h' (Preorder.le_of_lt (inv_pos_iff.mpr h))

theorem le_mul_inv_iff_mul_le (a b : R) {c : R} (h : 0 < c) : a ≤ b * c⁻¹ ↔ a * c ≤ b :=
  ⟨mul_le_of_le_mul_inv h, le_mul_inv_of_mul_le h⟩

private theorem mul_inv_le_iff_le_mul (a c : R) {b : R} (h : 0 < b) : a * b⁻¹ ≤ c ↔ a ≤ c * b := by
  have := (le_mul_inv_iff_mul_le a c (inv_pos_iff.mpr h)).symm
  simpa [Field.inv_inv] using this

private theorem mul_lt_of_lt_mul_inv {a b c : R} (h : 0 < c) (h' : a < b * c⁻¹) : a * c < b := by
  simpa [Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_gt h), Semiring.mul_one] using
    OrderedRing.mul_lt_mul_of_pos_right h' h

private theorem lt_mul_inv_of_mul_lt {a b c : R} (h : 0 < b) (h' : a * b < c) : a < c * b⁻¹ := by
  simpa [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_gt h), Semiring.mul_one] using
    OrderedRing.mul_lt_mul_of_pos_right h' (inv_pos_iff.mpr h)

theorem lt_mul_inv_iff_mul_lt (a b : R) {c : R} (h : 0 < c) : a < b * c⁻¹ ↔ a * c < b :=
  ⟨mul_lt_of_lt_mul_inv h, lt_mul_inv_of_mul_lt h⟩

theorem mul_inv_lt_iff_lt_mul (a c : R) {b : R} (h : 0 < b) : a * b⁻¹ < c ↔ a < c * b := by
  simpa [Field.inv_inv] using (lt_mul_inv_iff_mul_lt a c (inv_pos_iff.mpr h)).symm

private theorem le_mul_of_le_mul_inv {a b c : R} (h : c < 0) (h' : a ≤ b * c⁻¹) : b ≤ a * c := by
  simpa [Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_le_mul_of_nonpos_right h' (Preorder.le_of_lt h)

private theorem mul_le_of_mul_inv_le {a b c : R} (h : b < 0) (h' : a * b⁻¹ ≤ c) : c * b ≤ a := by
  simpa [Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_le_mul_of_nonpos_right h' (Preorder.le_of_lt h)

private theorem mul_inv_le_of_mul_le {a b c : R} (h : b < 0) (h' : a * b ≤ c) : c * b⁻¹ ≤ a := by
  simpa [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_le_mul_of_nonpos_right h' (Preorder.le_of_lt (inv_neg_iff.mpr h))

private theorem le_mul_inv_of_le_mul {a b c : R} (h : c < 0) (h' : a ≤ b * c) : b ≤ a * c⁻¹ := by
  simpa [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_le_mul_of_nonpos_right h' (Preorder.le_of_lt (inv_neg_iff.mpr h))

theorem le_mul_inv_iff_le_mul_of_neg (a b : R) {c : R} (h : c < 0) : a ≤ b * c⁻¹ ↔ b ≤ a * c :=
  ⟨le_mul_of_le_mul_inv h, le_mul_inv_of_le_mul h⟩

theorem mul_inv_le_iff_mul_le_of_neg (a c : R) {b : R} (h : b < 0) : a * b⁻¹ ≤ c ↔ c * b ≤ a :=
  ⟨mul_le_of_mul_inv_le h, mul_inv_le_of_mul_le h⟩

private theorem lt_mul_of_lt_mul_inv {a b c : R} (h : c < 0) (h' : a < b * c⁻¹) : b < a * c := by
  simpa [Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_lt_mul_of_neg_right h' h

private theorem mul_lt_of_mul_inv_lt {a b c : R} (h : b < 0) (h' : a * b⁻¹ < c) : c * b < a := by
  simpa [Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_lt_mul_of_neg_right h' h

private theorem mul_inv_lt_of_mul_lt {a b c : R} (h : b < 0) (h' : a * b < c) : c * b⁻¹ < a := by
  simpa [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_lt_mul_of_neg_right h' (inv_neg_iff.mpr h)

private theorem lt_mul_inv_of_lt_mul {a b c : R} (h : c < 0) (h' : a < b * c) : b < a * c⁻¹ := by
  simpa [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_lt h), Semiring.mul_one] using
    OrderedRing.mul_lt_mul_of_neg_right h' (inv_neg_iff.mpr h)

theorem lt_mul_inv_iff_lt_mul_of_neg (a b : R) {c : R} (h : c < 0) : a < b * c⁻¹ ↔ b < a * c :=
  ⟨lt_mul_of_lt_mul_inv h, lt_mul_inv_of_lt_mul h⟩

theorem mul_inv_lt_iff_mul_lt_of_neg (a c : R) {b : R} (h : b < 0) : a * b⁻¹ < c ↔ c * b < a :=
  ⟨mul_lt_of_mul_inv_lt h, mul_inv_lt_of_mul_lt h⟩

theorem mul_lt_mul_iff_of_pos_right {a b c : R} (h : 0 < c) : a * c < b * c ↔ a < b := by
  constructor
  · intro h'
    have := mul_lt_mul_of_pos_right h' (inv_pos_iff.mpr h)
    rwa [Semiring.mul_assoc, Semiring.mul_assoc, mul_inv_cancel (Preorder.ne_of_gt h),
      Semiring.mul_one, Semiring.mul_one] at this
  · exact (mul_lt_mul_of_pos_right · h)

theorem mul_lt_mul_iff_of_pos_left {a b c : R} (h : 0 < c) : c * a < c * b ↔ a < b := by
  constructor
  · intro h'
    have := mul_lt_mul_of_pos_left h' (inv_pos_iff.mpr h)
    rwa [← Semiring.mul_assoc, ← Semiring.mul_assoc, inv_mul_cancel (Preorder.ne_of_gt h),
      Semiring.one_mul, Semiring.one_mul] at this
  · exact (mul_lt_mul_of_pos_left · h)

theorem mul_lt_mul_iff_of_neg_right {a b c : R} (h : c < 0) : a * c < b * c ↔ b < a := by
  constructor
  · intro h'
    have := mul_lt_mul_of_neg_right h' (inv_neg_iff.mpr h)
    rwa [Semiring.mul_assoc, Semiring.mul_assoc, mul_inv_cancel (Preorder.ne_of_lt h),
      Semiring.mul_one, Semiring.mul_one] at this
  · exact (mul_lt_mul_of_neg_right · h)

theorem mul_lt_mul_iff_of_neg_left {a b c : R} (h : c < 0) : c * a < c * b ↔ b < a := by
  constructor
  · intro h'
    have := mul_lt_mul_of_neg_left h' (inv_neg_iff.mpr h)
    rwa [← Semiring.mul_assoc, ← Semiring.mul_assoc, inv_mul_cancel (Preorder.ne_of_lt h),
      Semiring.one_mul, Semiring.one_mul] at this
  · exact (mul_lt_mul_of_neg_left · h)

theorem mul_le_mul_iff_of_pos_right {a b c : R} (h : 0 < c) : a * c ≤ b * c ↔ a ≤ b := by
  constructor
  · intro h'
    have := mul_le_mul_of_nonneg_right h' (Preorder.le_of_lt (inv_pos_iff.mpr h))
    rwa [Semiring.mul_assoc, Semiring.mul_assoc, mul_inv_cancel (Preorder.ne_of_gt h),
      Semiring.mul_one, Semiring.mul_one] at this
  · exact (mul_le_mul_of_nonneg_right · (Preorder.le_of_lt h))

theorem mul_le_mul_iff_of_pos_left {a b c : R} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b := by
  constructor
  · intro h'
    have := mul_le_mul_of_nonneg_left h' (Preorder.le_of_lt (inv_pos_iff.mpr h))
    rwa [← Semiring.mul_assoc, ← Semiring.mul_assoc, inv_mul_cancel (Preorder.ne_of_gt h),
      Semiring.one_mul, Semiring.one_mul] at this
  · exact (mul_le_mul_of_nonneg_left · (Preorder.le_of_lt h))

theorem mul_le_mul_iff_of_neg_right {a b c : R} (h : c < 0) : a * c ≤ b * c ↔ b ≤ a := by
  constructor
  · intro h'
    have := mul_le_mul_of_nonpos_right h' (Preorder.le_of_lt (inv_neg_iff.mpr h))
    rwa [Semiring.mul_assoc, Semiring.mul_assoc, mul_inv_cancel (Preorder.ne_of_lt h),
      Semiring.mul_one, Semiring.mul_one] at this
  · exact (mul_le_mul_of_nonpos_right · (Preorder.le_of_lt h))

theorem mul_le_mul_iff_of_neg_left {a b c : R} (h : c < 0) : c * a ≤ c * b ↔ b ≤ a := by
  constructor
  · intro h'
    have := mul_le_mul_of_nonpos_left h' (Preorder.le_of_lt (inv_neg_iff.mpr h))
    rwa [← Semiring.mul_assoc, ← Semiring.mul_assoc, inv_mul_cancel (Preorder.ne_of_lt h),
      Semiring.one_mul, Semiring.one_mul] at this
  · exact (mul_le_mul_of_nonpos_left · (Preorder.le_of_lt h))

end Field.IsOrdered

end Lean.Grind
