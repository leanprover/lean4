/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Int.Order
import Init.Omega


/-!
# Further lemmas about `Int` relying on `omega` automation.
-/

namespace Int

@[simp] theorem toNat_sub' (a : Int) (b : Nat) : (a - b).toNat = a.toNat - b := by
  symm
  simp only [Int.toNat]
  split <;> rename_i x a
  · simp only [Int.ofNat_eq_coe]
    split <;> rename_i y b h
    · simp at h
      omega
    · simp [Int.negSucc_eq] at h
      omega
  · simp only [Nat.zero_sub]
    split <;> rename_i y b h
    · simp [Int.negSucc_eq] at h
      omega
    · rfl

@[simp] theorem toNat_sub_max_self (a : Int) : (a - max a 0).toNat = 0 := by
  simp [toNat]
  split <;> simp_all <;> omega

@[simp] theorem toNat_sub_self_max (a : Int) : (a - max 0 a).toNat = 0 := by
  simp [toNat]
  split <;> simp_all <;> omega

theorem bmod_neg_iff {m : Nat} {x : Int} (h2 : -m ≤ x) (h1 : x < m) :
    (x.bmod m) < 0 ↔ (-(m / 2) ≤ x ∧ x < 0) ∨ ((m + 1) / 2 ≤ x) := by
  simp only [Int.bmod_def]
  by_cases xpos : 0 ≤ x
  · rw [Int.emod_eq_of_lt xpos (by omega)]; omega
  · rw [Int.add_emod_self.symm, Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem bmod_eq_of_le_of_lt {x : Int} {y : Nat} (hge : -y ≤ x * 2) (hlt : x * 2 < y) :
    x.bmod y = x := by
  simp only [Int.bmod_def]
  rcases x
  · rw [Int.emod_eq_of_lt (by simp only [ofNat_eq_coe]; omega) (by omega)]; omega
  · rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem mul_le_mul_self {x y : Int} {s : Nat} (hx : x.natAbs ≤ s) (hy : y.natAbs ≤ s) :
    x * y ≤ s * s := by
  rcases s with _|s
  · simp [show x = 0 by omega]
  · have := Nat.mul_pos (n := (s + 1)) (m := (s + 1)) (by omega) (by omega)
    by_cases hx : 0 < x <;> by_cases hy : 0 < y
    · exact Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
    · have : x * y ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega); omega
    · have : x * y ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega); omega
    · have : -x * -y ≤ (s + 1) * (s + 1) := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      simp_all

theorem neg_mul_self_le_mul {x y : Int} {s : Nat} (lbx : -s ≤ x) (ubx : x < s) (lby : -s ≤ y) (uby : y < s) :
      -(s * s) ≤ x * y := by
  have := Nat.mul_pos (n := s) (m := s) (by omega) (by omega)
  by_cases 0 ≤ x <;> by_cases 0 ≤ y
  · have : 0 ≤ x * y := Int.mul_nonneg (by omega) (by omega); omega
  · rw [← Int.neg_mul, Int.mul_comm (a := x)]; exact Int.mul_le_mul_neg (by omega) (by omega) (by omega) (by omega)
  · rw [← Int.neg_mul]; exact Int.mul_le_mul_neg (by omega) (by omega) (by omega) (by omega)
  · have : 0 < x * y := Int.mul_pos_of_neg_of_neg (by omega) (by omega); omega

end Int
