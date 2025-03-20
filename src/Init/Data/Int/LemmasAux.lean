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

/-! ### miscellaneous lemmas -/

@[simp] theorem natCast_le_zero : {n : Nat} → (n : Int) ≤ 0 ↔ n = 0 := by omega

protected theorem sub_eq_iff_eq_add {b a c : Int} : a - b = c ↔ a = c + b := by omega
protected theorem sub_eq_iff_eq_add' {b a c : Int} : a - b = c ↔ a = b + c := by omega

@[simp] protected theorem neg_nonpos_iff (i : Int) : -i ≤ 0 ↔ 0 ≤ i := by omega

@[simp] theorem zero_le_ofNat (n : Nat) : 0 ≤ ((no_index (OfNat.ofNat n)) : Int) :=
  ofNat_nonneg _

@[simp] theorem neg_natCast_le_natCast (n m : Nat) : -(n : Int) ≤ (m : Int) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

@[simp] theorem neg_natCast_le_ofNat (n m : Nat) : -(n : Int) ≤ (no_index (OfNat.ofNat m)) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

@[simp] theorem neg_ofNat_le_ofNat (n m : Nat) : -(no_index (OfNat.ofNat n)) ≤ (no_index (OfNat.ofNat m)) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

@[simp] theorem neg_ofNat_le_natCast (n m : Nat) : -(no_index (OfNat.ofNat n)) ≤ (m : Int) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

/-! ### toNat -/

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

@[simp] theorem toNat_eq_zero : ∀ {n : Int}, n.toNat = 0 ↔ n ≤ 0 := by omega

@[simp] theorem toNat_le {m : Int} {n : Nat} : m.toNat ≤ n ↔ m ≤ n := by omega
@[simp] theorem toNat_lt' {m : Int} {n : Nat} (hn : 0 < n) : m.toNat < n ↔ m < n := by omega

/-! ### natAbs -/

theorem eq_zero_of_dvd_of_natAbs_lt_natAbs {d n : Int} (h : d ∣ n) (h₁ : n.natAbs < d.natAbs) :
    n = 0 := by
  obtain ⟨a, rfl⟩ := h
  rw [natAbs_mul] at h₁
  suffices ¬ 0 < a.natAbs by simp [Int.natAbs_eq_zero.1 (Nat.eq_zero_of_not_pos this)]
  exact fun h => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right d.natAbs h) h₁)

/-! ### min and max -/

@[simp] protected theorem min_assoc : ∀ (a b c : Int), min (min a b) c = min a (min b c) := by omega
instance : Std.Associative (α := Nat) min := ⟨Nat.min_assoc⟩

@[simp] protected theorem min_self_assoc {m n : Int} : min m (min m n) = min m n := by
  rw [← Int.min_assoc, Int.min_self]

@[simp] protected theorem min_self_assoc' {m n : Int} : min n (min m n) = min n m := by
  rw [Int.min_comm m n, ← Int.min_assoc, Int.min_self]

@[simp] protected theorem max_assoc (a b c : Int) : max (max a b) c = max a (max b c) := by omega
instance : Std.Associative (α := Nat) max := ⟨Nat.max_assoc⟩

@[simp] protected theorem max_self_assoc {m n : Int} : max m (max m n) = max m n := by
  rw [← Int.max_assoc, Int.max_self]

@[simp] protected theorem max_self_assoc' {m n : Int} : max n (max m n) = max n m := by
  rw [Int.max_comm m n, ← Int.max_assoc, Int.max_self]

protected theorem max_min_distrib_left (a b c : Int) : max a (min b c) = min (max a b) (max a c) := by omega

protected theorem min_max_distrib_left (a b c : Int) : min a (max b c) = max (min a b) (min a c) := by omega

protected theorem max_min_distrib_right (a b c : Int) :
    max (min a b) c = min (max a c) (max b c) := by omega

protected theorem min_max_distrib_right (a b c : Int) :
    min (max a b) c = max (min a c) (min b c) := by omega

protected theorem sub_min_sub_right (a b c : Int) : min (a - c) (b - c) = min a b - c := by omega

protected theorem sub_max_sub_right (a b c : Int) : max (a - c) (b - c) = max a b - c := by omega

protected theorem sub_min_sub_left (a b c : Int) : min (a - b) (a - c) = a - max b c := by omega

protected theorem sub_max_sub_left (a b c : Int) : max (a - b) (a - c) = a - min b c := by omega

/-! ### bmod -/

theorem bmod_neg_iff {m : Nat} {x : Int} (h2 : -m ≤ x) (h1 : x < m) :
    (x.bmod m) < 0 ↔ (-(m / 2) ≤ x ∧ x < 0) ∨ ((m + 1) / 2 ≤ x) := by
  simp only [Int.bmod_def]
  by_cases xpos : 0 ≤ x
  · rw [Int.emod_eq_of_lt xpos (by omega)]; omega
  · rw [Int.add_emod_self.symm, Int.emod_eq_of_lt (by omega) (by omega)]; omega

theorem bmod_eq_self_of_le {n : Int} {m : Nat} (hn' : -(m / 2) ≤ n) (hn : n < (m + 1) / 2) :
    n.bmod m = n := by
  rw [← Int.sub_eq_zero]
  have := le_bmod (x := n) (m := m) (by omega)
  have := bmod_lt (x := n) (m := m) (by omega)
  apply eq_zero_of_dvd_of_natAbs_lt_natAbs Int.dvd_bmod_sub_self
  omega

theorem bmod_bmod_of_dvd {a : Int} {n m : Nat} (hnm : n ∣ m) :
    (a.bmod m).bmod n = a.bmod n := by
  rw [← Int.sub_eq_iff_eq_add.2 (bmod_add_bdiv a m).symm]
  obtain ⟨k, rfl⟩ := hnm
  simp [Int.mul_assoc]

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
