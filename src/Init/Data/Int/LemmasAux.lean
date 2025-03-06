/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Int.Order
import Init.Data.Int.DivMod.Lemmas
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

@[simp] theorem natCast_le_zero : {n : Nat} → (n : Int) ≤ 0 ↔ n = 0 := by omega

@[simp] theorem toNat_eq_zero : ∀ {n : Int}, n.toNat = 0 ↔ n ≤ 0 := by omega

theorem eq_zero_of_dvd_of_natAbs_lt_natAbs {d n : Int} (h : d ∣ n) (h₁ : n.natAbs < d.natAbs) :
    n = 0 := by
  obtain ⟨a, rfl⟩ := h
  rw [natAbs_mul] at h₁
  suffices ¬ 0 < a.natAbs by simp [Int.natAbs_eq_zero.1 (Nat.eq_zero_of_not_pos this)]
  exact fun h => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right d.natAbs h) h₁)

theorem bmod_eq_self_of_le {n : Int} {m : Nat} (hn' : -(m / 2) ≤ n) (hn : n < (m + 1) / 2) :
    n.bmod m = n := by
  rw [← Int.sub_eq_zero]
  have := le_bmod (x := n) (m := m) (by omega)
  have := bmod_lt (x := n) (m := m) (by omega)
  apply eq_zero_of_dvd_of_natAbs_lt_natAbs Int.dvd_bmod_sub_self
  omega

protected theorem sub_eq_iff_eq_add {b a c : Int} : a - b = c ↔ a = c + b := by omega
protected theorem sub_eq_iff_eq_add' {b a c : Int} : a - b = c ↔ a = b + c := by omega

theorem bmod_bmod_of_dvd {a : Int} {n m : Nat} (hnm : n ∣ m) :
    (a.bmod m).bmod n = a.bmod n := by
  rw [← Int.sub_eq_iff_eq_add.2 (bmod_add_bdiv a m).symm]
  obtain ⟨k, rfl⟩ := hnm
  simp [Int.mul_assoc]

@[simp] theorem toNat_le {m : Int} {n : Nat} : m.toNat ≤ n ↔ m ≤ n := by omega
@[simp] theorem toNat_lt' {m : Int} {n : Nat} (hn : 0 < n) : m.toNat < n ↔ m < n := by omega

end Int
