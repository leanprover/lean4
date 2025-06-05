/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.Order
import Init.Grind.Module.Basic
import Init.Grind.Ordered.Order

namespace Lean.Grind

class IntModule.IsOrdered (M : Type u) [Preorder M] [IntModule M] where
  neg_le_iff : ∀ a b : M, -a ≤ b ↔ -b ≤ a
  add_le_left : ∀ {a b : M}, a ≤ b → (c : M) → a + c ≤ b + c
  hmul_pos : ∀ (k : Int) {a : M}, 0 < a → (0 < k ↔ 0 < k * a)
  hmul_nonneg : ∀ {k : Int} {a : M}, 0 ≤ k → 0 ≤ a → 0 ≤ k * a

namespace IntModule.IsOrdered

variable {M : Type u} [Preorder M] [IntModule M] [IntModule.IsOrdered M]

theorem le_neg_iff {a b : M} : a ≤ -b ↔ b ≤ -a := by
  conv => lhs; rw [← neg_neg a]
  rw [neg_le_iff, neg_neg]

theorem neg_lt_iff {a b : M} : -a < b ↔ -b < a := by
  simp [Preorder.lt_iff_le_not_le]
  rw [neg_le_iff, le_neg_iff]

theorem lt_neg_iff {a b : M} : a < -b ↔ b < -a := by
  conv => lhs; rw [← neg_neg a]
  rw [neg_lt_iff, neg_neg]

theorem neg_nonneg_iff {a : M} : 0 ≤ -a ↔ a ≤ 0 := by
  rw [le_neg_iff, neg_zero]

theorem neg_pos_iff {a : M} : 0 < -a ↔ a < 0 := by
  rw [lt_neg_iff, neg_zero]

theorem add_lt_left {a b : M} (h : a < b) (c : M) : a + c < b + c := by
  simp [Preorder.lt_iff_le_not_le] at h ⊢
  constructor
  · exact add_le_left h.1 _
  · intro w
    apply h.2
    replace w := add_le_left w (-c)
    rw [add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at w
    exact w

theorem add_le_right (a : M) {b c : M} (h : b ≤ c) : a + b ≤ a + c := by
  rw [add_comm a b, add_comm a c]
  exact add_le_left h a

theorem add_lt_right (a : M) {b c : M} (h : b < c) : a + b < a + c := by
  rw [add_comm a b, add_comm a c]
  exact add_lt_left h a

theorem hmul_neg (k : Int) {a : M} (h : a < 0) : 0 < k ↔ k * a < 0 := by
  simpa [IntModule.hmul_neg, neg_pos_iff] using hmul_pos k (neg_pos_iff.mpr h)

theorem hmul_nonpos {k : Int} {a : M} (hk : 0 ≤ k) (ha : a ≤ 0) : k * a ≤ 0 := by
  simpa [IntModule.hmul_neg, neg_nonneg_iff] using hmul_nonneg hk (neg_nonneg_iff.mpr ha)

end IntModule.IsOrdered

end Lean.Grind
