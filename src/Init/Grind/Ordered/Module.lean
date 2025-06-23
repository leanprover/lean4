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

/--
Addition is compatible with a preorder if `a ≤ b ↔ a + c ≤ b + c`.
-/
class OrderedAdd (M : Type u) [HAdd M M M] [Preorder M] where
  /-- `a + c ≤ b + c` iff `a ≤ b`. -/
  add_le_left_iff : ∀ {a b : M} (c : M), a ≤ b ↔ a + c ≤ b + c

namespace OrderedAdd

open NatModule

section

variable {M : Type u} [Preorder M] [NatModule M] [OrderedAdd M]

theorem add_le_right_iff {a b : M} (c : M) : a ≤ b ↔ c + a ≤ c + b := by
  rw [add_comm c a, add_comm c b, add_le_left_iff]

theorem hmul_le_hmul {k : Nat} {a b : M} (h : a ≤ b) : k * a ≤ k * b := by
  induction k with
  | zero => simp [zero_hmul, Preorder.le_refl]
  | succ k ih =>
    rw [add_hmul, one_hmul, add_hmul, one_hmul]
    exact Preorder.le_trans ((add_le_left_iff a).mp ih) ((add_le_right_iff (k * b)).mp h)

theorem add_le_left {a b : M} (h : a ≤ b) (c : M) : a + c ≤ b + c :=
  (add_le_left_iff c).mp h

theorem add_le_right {a b : M} (c : M) (h : a ≤ b) : c + a ≤ c + b :=
  (add_le_right_iff c).mp h

theorem add_lt_left {a b : M} (h : a < b) (c : M) : a + c < b + c := by
  simp only [Preorder.lt_iff_le_not_le] at h ⊢
  constructor
  · exact add_le_left h.1 _
  · intro w
    apply h.2
    exact (add_le_left_iff c).mpr w

theorem add_lt_right {a b : M} (c : M) (h : a < b) : c + a < c + b := by
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

theorem hmul_lt_hmul_iff (k : Nat) {a b : M} (h : a < b) : k * a < k * b ↔ 0 < k := by
  induction k with
  | zero => simp [zero_hmul, Preorder.lt_irrefl]
  | succ k ih =>
    rw [add_hmul, one_hmul, add_hmul, one_hmul]
    simp only [Nat.zero_lt_succ, iff_true]
    by_cases hk : 0 < k
    · simp only [hk, iff_true] at ih
      exact Preorder.lt_trans ((add_lt_left_iff a).mp ih) ((add_lt_right_iff (k * b)).mp h)
    · simp [Nat.eq_zero_of_not_pos hk, zero_hmul, zero_add, h]

theorem hmul_pos_iff {k : Nat} {a : M} (h : 0 < a) : 0 < k * a ↔ 0 < k:= by
  rw [← hmul_lt_hmul_iff k h, hmul_zero]

theorem hmul_nonneg {k : Nat} {a : M} (h : 0 ≤ a) : 0 ≤ k * a := by
  have := hmul_le_hmul (k := k) h
  rwa [hmul_zero] at this

theorem hmul_le_hmul_of_le_of_le_of_nonneg
    {k₁ k₂ : Nat} {x y : M} (hk : k₁ ≤ k₂) (h : x ≤ y) (w : 0 ≤ x) :
    k₁ * x ≤ k₂ * y := by
  apply Preorder.le_trans
  · change k₁ * x ≤ k₂ * x
    obtain ⟨k', rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [add_hmul]
    conv => lhs; rw [← add_zero (k₁ * x)]
    rw [← add_le_right_iff]
    exact hmul_nonneg w
  · exact hmul_le_hmul h

theorem add_le_add {a b c d : M} (hab : a ≤ b) (hcd : c ≤ d) : a + c ≤ b + d :=
  Preorder.le_trans (add_le_right a hcd) (add_le_left hab d)

end

section

variable {M : Type u} [Preorder M] [IntModule M] [OrderedAdd M]

theorem neg_le_iff {a b : M} : -a ≤ b ↔ -b ≤ a := by
  rw [OrderedAdd.add_le_left_iff a, IntModule.neg_add_cancel]
  conv => rhs; rw [OrderedAdd.add_le_left_iff b, IntModule.neg_add_cancel]
  rw [add_comm]

end
section

variable {M : Type u} [Preorder M] [IntModule M] [OrderedAdd M]

theorem hmul_int_pos_iff (k : Int) {x : M} (h : 0 < x) : 0 < k * x ↔ 0 < k :=
  match k with
  | (k + 1 : Nat) => by
    simpa [IntModule.hmul_zero, ← IntModule.hmul_nat] using hmul_lt_hmul_iff (k := k + 1) h
  | (0 : Nat) => by simp [IntModule.zero_hmul]; exact Preorder.lt_irrefl 0
  | -(k + 1 : Nat) => by
    have : ¬ (k : Int) + 1 < 0 := by omega
    simp [this]; clear this
    rw [IntModule.neg_hmul]
    rw [Preorder.lt_iff_le_not_le]
    simp
    intro h'
    rw [OrderedAdd.neg_le_iff, IntModule.neg_zero]
    simpa [IntModule.hmul_zero, ← IntModule.hmul_nat] using
      hmul_le_hmul (k := k + 1) (Preorder.le_of_lt h)

theorem hmul_int_nonneg {k : Int} {x : M} (h : 0 ≤ k) (hx : 0 ≤ x) : 0 ≤ k * x :=
  match k, h with
  | (k : Nat), _ => by
    simpa [IntModule.hmul_nat] using OrderedAdd.hmul_nonneg hx

end

variable {M : Type u} [Preorder M] [IntModule M] [OrderedAdd M]

open IntModule

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

theorem sub_nonneg_iff {a b : M} : 0 ≤ a - b ↔ b ≤ a := by
  rw [add_le_left_iff b, IntModule.zero_add, sub_add_cancel]

theorem sub_pos_iff {a b : M} : 0 < a - b ↔ b < a := by
  rw [add_lt_left_iff b, IntModule.zero_add, sub_add_cancel]

theorem hmul_int_neg_iff (k : Int) {a : M} (h : a < 0) : k * a < 0 ↔ 0 < k := by
  simpa [IntModule.hmul_neg, neg_pos_iff] using hmul_int_pos_iff k (neg_pos_iff.mpr h)

theorem hmul_int_nonpos {k : Int} {a : M} (hk : 0 ≤ k) (ha : a ≤ 0) : k * a ≤ 0 := by
  simpa [IntModule.hmul_neg, neg_nonneg_iff] using hmul_int_nonneg hk (neg_nonneg_iff.mpr ha)

theorem hmul_int_le_hmul_int {a b : M} {k : Int} (hk : 0 ≤ k) (h : a ≤ b) : k * a ≤ k * b := by
  simpa [hmul_sub, sub_nonneg_iff] using hmul_int_nonneg hk (sub_nonneg_iff.mpr h)

theorem hmul_int_lt_hmul_int_iff (k : Int) {a b : M} (h : a < b) : k * a < k * b ↔ 0 < k := by
  simpa [hmul_sub, sub_pos_iff] using hmul_int_pos_iff k (sub_pos_iff.mpr h)

theorem hmul_int_le_hmul_int_of_le_of_le_of_nonneg_of_nonneg
    {k₁ k₂ : Int} {x y : M} (hk : k₁ ≤ k₂) (h : x ≤ y) (w : 0 ≤ k₁) (w' : 0 ≤ x) :
    k₁ * x ≤ k₂ * y := by
  apply Preorder.le_trans
  · have : 0 ≤ k₁ * (y - x) := hmul_int_nonneg w (sub_nonneg_iff.mpr h)
    rwa [IntModule.hmul_sub, sub_nonneg_iff] at this
  · have : 0 ≤ (k₂ - k₁) * y := hmul_int_nonneg (Int.sub_nonneg.mpr hk) (Preorder.le_trans w' h)
    rwa [IntModule.sub_hmul, sub_nonneg_iff] at this

end OrderedAdd

end Lean.Grind
