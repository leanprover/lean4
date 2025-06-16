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

class NatModule.IsOrdered (M : Type u) [Preorder M] [NatModule M] where
  add_le_left_iff : ∀ {a b : M} (c : M), a ≤ b ↔ a + c ≤ b + c
  hmul_pos : ∀ (k : Nat) {a : M}, 0 < a → (0 < k ↔ 0 < k * a)
  hmul_nonneg : ∀ {k : Nat} {a : M}, 0 ≤ a → 0 ≤ k * a

class IntModule.IsOrdered (M : Type u) [Preorder M] [IntModule M] where
  neg_le_iff : ∀ a b : M, -a ≤ b ↔ -b ≤ a
  add_le_left : ∀ {a b : M}, a ≤ b → (c : M) → a + c ≤ b + c
  hmul_pos : ∀ (k : Int) {a : M}, 0 < a → (0 < k ↔ 0 < k * a)
  hmul_nonneg : ∀ {k : Int} {a : M}, 0 ≤ k → 0 ≤ a → 0 ≤ k * a

namespace NatModule.IsOrdered

variable {M : Type u} [Preorder M] [NatModule M] [NatModule.IsOrdered M]

theorem add_le_right_iff {a b : M} (c : M) : a ≤ b ↔ c + a ≤ c + b := by
  rw [add_comm c a, add_comm c b,add_le_left_iff]

theorem add_le_left {a b : M} (h : a ≤ b) (c : M) : a + c ≤ b + c :=
  (add_le_left_iff c).mp h

theorem add_le_right {a b : M} (h : a ≤ b) (c : M) : c + a ≤ c + b :=
  (add_le_right_iff c).mp h

theorem add_lt_left {a b : M} (h : a < b) (c : M) : a + c < b + c := by
  simp only [Preorder.lt_iff_le_not_le] at h ⊢
  constructor
  · exact add_le_left h.1 _
  · intro w
    apply h.2
    exact (add_le_left_iff c).mpr w

theorem add_lt_right {a b : M} (h : a < b) (c : M) : c + a < c + b := by
  rw [add_comm c a, add_comm c b]
  exact add_lt_left h c

theorem add_lt_left_iff {a b : M} (c : M) : a < b ↔ a + c < b + c := by
  constructor
  · exact fun h => add_lt_left h c
  · intro w
    simp only [Preorder.lt_iff_le_not_le] at w ⊢
    constructor
    · exact (add_le_left_iff c).mpr w.1
    · intro h
      exact w.2 ((add_le_left_iff c).mp h)

theorem add_lt_right_iff {a b : M} (c : M) : a < b ↔ c + a < c + b := by
  rw [add_comm c a, add_comm c b, add_lt_left_iff]

end NatModule.IsOrdered

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
  simp only [Preorder.lt_iff_le_not_le] at h ⊢
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

theorem add_le_left_iff {a b : M} (c : M) : a ≤ b ↔ a + c ≤ b + c := by
  constructor
  · intro w
    exact add_le_left w c
  · intro w
    have := add_le_left w (-c)
    rwa [add_assoc, add_neg_cancel, add_zero, add_assoc, add_neg_cancel, add_zero] at this

theorem add_le_right_iff {a b : M} (c : M) : a ≤ b ↔ c + a ≤ c + b := by
  constructor
  · intro w
    exact add_le_right c w
  · intro w
    have := add_le_right (-c) w
    rwa [← add_assoc, neg_add_cancel, zero_add, ← add_assoc, neg_add_cancel, zero_add] at this

theorem add_lt_left_iff {a b : M} (c : M) : a < b ↔ a + c < b + c := by
  constructor
  · intro w
    exact add_lt_left w c
  · intro w
    have := add_lt_left w (-c)
    rwa [add_assoc, add_neg_cancel, add_zero, add_assoc, add_neg_cancel, add_zero] at this

theorem add_lt_right_iff {a b : M} (c : M) : a < b ↔ c + a < c + b := by
  constructor
  · intro w
    exact add_lt_right c w
  · intro w
    have := add_lt_right (-c) w
    rwa [← add_assoc, neg_add_cancel, zero_add, ← add_assoc, neg_add_cancel, zero_add] at this

theorem sub_nonneg_iff {a b : M} : 0 ≤ a - b ↔ b ≤ a := by
  rw [add_le_left_iff b, zero_add, sub_add_cancel]

theorem hmul_neg (k : Int) {a : M} (h : a < 0) : 0 < k ↔ k * a < 0 := by
  simpa [IntModule.hmul_neg, neg_pos_iff] using hmul_pos k (neg_pos_iff.mpr h)

theorem hmul_nonpos {k : Int} {a : M} (hk : 0 ≤ k) (ha : a ≤ 0) : k * a ≤ 0 := by
  simpa [IntModule.hmul_neg, neg_nonneg_iff] using hmul_nonneg hk (neg_nonneg_iff.mpr ha)

theorem hmul_le_hmul_of_le_of_le_of_nonneg_of_nonneg
    {k₁ k₂ : Int} {x y : M} (hk : k₁ ≤ k₂) (h : x ≤ y) (w : 0 ≤ k₁) (w' : 0 ≤ x) :
    k₁ * x ≤ k₂ * y := by
  apply Preorder.le_trans
  · have : 0 ≤ k₁ * (y - x) := hmul_nonneg w (sub_nonneg_iff.mpr h)
    rwa [IntModule.hmul_sub, sub_nonneg_iff] at this
  · have : 0 ≤ (k₂ - k₁) * y := hmul_nonneg (Int.sub_nonneg.mpr hk) (Preorder.le_trans w' h)
    rwa [IntModule.sub_hmul, sub_nonneg_iff] at this

theorem add_le_add {a b c d : M} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  Preorder.le_trans (add_le_right a hcd) (add_le_left hab d)

end IntModule.IsOrdered

end Lean.Grind
