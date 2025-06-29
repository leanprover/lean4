/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Int.Order
public import Init.Data.Int.Pow
public import Init.Data.Int.DivMod.Lemmas
public import Init.Omega

public section


/-!
# Further lemmas about `Int` relying on `omega` automation.
-/

namespace Int

/-! ### miscellaneous lemmas -/

@[simp] theorem natCast_le_zero : {n : Nat} → (n : Int) ≤ 0 ↔ n = 0 := by omega

@[simp] protected theorem neg_nonpos_iff (i : Int) : -i ≤ 0 ↔ 0 ≤ i := by omega

@[simp] theorem zero_le_ofNat (n : Nat) : 0 ≤ ((no_index (OfNat.ofNat n)) : Int) :=
  natCast_nonneg _

@[simp] theorem neg_natCast_le_natCast (n m : Nat) : -(n : Int) ≤ (m : Int) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

@[simp] theorem neg_natCast_le_ofNat (n m : Nat) : -(n : Int) ≤ (no_index (OfNat.ofNat m)) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

@[simp] theorem neg_ofNat_le_ofNat (n m : Nat) : -(no_index (OfNat.ofNat n)) ≤ (no_index (OfNat.ofNat m)) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

@[simp] theorem neg_ofNat_le_natCast (n m : Nat) : -(no_index (OfNat.ofNat n)) ≤ (m : Int) :=
  Int.le_trans (by simp) (ofNat_zero_le m)

theorem neg_lt_self_iff {n : Int} : -n < n ↔ 0 < n := by
  omega

protected theorem ofNat_add_out (m n : Nat) : ↑m + ↑n = (↑(m + n) : Int) := rfl

protected theorem ofNat_mul_out (m n : Nat) : ↑m * ↑n = (↑(m * n) : Int) := rfl

protected theorem ofNat_add_one_out (n : Nat) : ↑n + (1 : Int) = ↑(Nat.succ n) := rfl

@[simp] theorem ofNat_eq_natCast (n : Nat) : Int.ofNat n = n := rfl

@[norm_cast] theorem natCast_inj {m n : Nat} : (m : Int) = (n : Int) ↔ m = n := ofNat_inj

@[norm_cast]
protected theorem natCast_sub {n m : Nat} : n ≤ m → (↑(m - n) : Int) = ↑m - ↑n := ofNat_sub

theorem natCast_ne_zero {n : Nat} : (n : Int) ≠ 0 ↔ n ≠ 0 := by omega

theorem natCast_ne_zero_iff_pos {n : Nat} : (n : Int) ≠ 0 ↔ 0 < n := by omega

theorem natCast_succ_pos (n : Nat) : 0 < (n.succ : Int) := natCast_pos.2 n.succ_pos

@[simp high] theorem natCast_nonpos_iff {n : Nat} : (n : Int) ≤ 0 ↔ n = 0 := by omega

@[simp] theorem sign_natCast_add_one (n : Nat) : sign (n + 1) = 1 := rfl

@[simp, norm_cast] theorem cast_id {n : Int} : Int.cast n = n := rfl

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
@[simp] theorem lt_toNat {m : Nat} {n : Int} : m < toNat n ↔ m < n := by omega
theorem lt_of_toNat_lt {a b : Int} (h : toNat a < toNat b) : a < b := by omega

theorem toNat_sub_of_le {a b : Int} (h : b ≤ a) : (toNat (a - b) : Int) = a - b := by omega

theorem pos_iff_toNat_pos {n : Int} : 0 < n ↔ 0 < n.toNat := by
  omega

theorem natCast_toNat_eq_self {a : Int} : a.toNat = a ↔ 0 ≤ a := by omega

@[deprecated natCast_toNat_eq_self (since := "2025-04-16")]
theorem ofNat_toNat_eq_self {a : Int} : a.toNat = a ↔ 0 ≤ a := natCast_toNat_eq_self

theorem eq_natCast_toNat {a : Int} : a = a.toNat ↔ 0 ≤ a := by omega

@[deprecated eq_natCast_toNat (since := "2025-04-16")]
theorem eq_ofNat_toNat {a : Int} : a = a.toNat ↔ 0 ≤ a := eq_natCast_toNat

theorem toNat_le_toNat {n m : Int} (h : n ≤ m) : n.toNat ≤ m.toNat := by omega
theorem toNat_lt_toNat {n m : Int} (hn : 0 < m) : n.toNat < m.toNat ↔ n < m := by omega

/-! ### min and max -/

@[simp] protected theorem min_assoc : ∀ (a b c : Int), min (min a b) c = min a (min b c) := by omega
instance : Std.Associative (α := Int) min := ⟨Int.min_assoc⟩

@[simp] protected theorem min_self_assoc {m n : Int} : min m (min m n) = min m n := by
  rw [← Int.min_assoc, Int.min_self]

@[simp] protected theorem min_self_assoc' {m n : Int} : min n (min m n) = min n m := by
  rw [Int.min_comm m n, ← Int.min_assoc, Int.min_self]

@[simp] protected theorem max_assoc (a b c : Int) : max (max a b) c = max a (max b c) := by omega
instance : Std.Associative (α := Int) max := ⟨Int.max_assoc⟩

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

/-! ## mul -/

theorem mul_le_mul_of_natAbs_le {x y : Int} {s t : Nat} (hx : x.natAbs ≤ s) (hy : y.natAbs ≤ t) :
    x * y ≤ s * t := by
  by_cases 0 < s ∧ 0 < t
  · have := Nat.mul_pos (n := s) (m := t) (by omega) (by omega)
    by_cases hx : 0 < x <;> by_cases hy : 0 < y
    · apply Int.mul_le_mul <;> omega
    · have : x * y ≤ 0 := Int.mul_nonpos_of_nonneg_of_nonpos (by omega) (by omega); omega
    · have : x * y ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by omega); omega
    · have : -x * -y ≤ s * t := Int.mul_le_mul (by omega) (by omega) (by omega) (by omega)
      simp [Int.neg_mul_neg] at this
      norm_cast
  · have : (x = 0 ∨ y = 0) → x * y = 0 := by simp [Int.mul_eq_zero]
    norm_cast
    omega

/--
This is a generalization of `a ≤ c` and `b ≤ d` implying `a * b ≤ c * d` for natural numbers,
appropriately generalized to integers when `b` is nonnegative and `c` is nonpositive.
-/
theorem mul_le_mul_of_le_of_le_of_nonneg_of_nonpos {a b c d : Int}
    (hac : a ≤ c) (hbd : d ≤ b) (hb : 0 ≤ b) (hc : c ≤ 0) : a * b ≤ c * d :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_right hac hb) (Int.mul_le_mul_of_nonpos_left hc hbd)

theorem mul_le_mul_of_le_of_le_of_nonneg_of_nonneg {a b c d : Int}
    (hac : a ≤ c) (hbd : b ≤ d) (hb : 0 ≤ b) (hc : 0 ≤ c) : a * b ≤ c * d :=
  Int.le_trans (Int.mul_le_mul_of_nonneg_right hac hb) (Int.mul_le_mul_of_nonneg_left hbd hc)

theorem mul_le_mul_of_le_of_le_of_nonpos_of_nonpos {a b c d : Int}
    (hac : c ≤ a) (hbd : d ≤ b) (hb : b ≤ 0) (hc : c ≤ 0) : a * b ≤ c * d :=
  Int.le_trans (Int.mul_le_mul_of_nonpos_right hac hb) (Int.mul_le_mul_of_nonpos_left hc hbd)

theorem mul_le_mul_of_le_of_le_of_nonpos_of_nonneg {a b c d : Int}
    (hac : c ≤ a) (hbd : b ≤ d) (hb : b ≤ 0) (hc : 0 ≤ c) : a * b ≤ c * d :=
  Int.le_trans (Int.mul_le_mul_of_nonpos_right hac hb) (Int.mul_le_mul_of_nonneg_left hbd hc)

/--
A corollary of |s| ≤ x, and |t| ≤ y, then |s * t| ≤ x * y,
-/
theorem neg_mul_le_mul {x y : Int} {s t : Nat} (lbx : -s ≤ x) (ubx : x < s) (lby : -t ≤ y) (uby : y < t) :
      -(s * t) ≤ x * y := by
  have := Nat.mul_pos (n := s) (m := t) (by omega) (by omega)
  by_cases 0 ≤ x <;> by_cases 0 ≤ y
  · have : 0 ≤ x * y := by apply Int.mul_nonneg <;> omega
    norm_cast
    omega
  · rw [Int.mul_comm (a := x), Int.mul_comm (a := (s : Int)), ← Int.neg_mul]; apply Int.mul_le_mul_of_le_of_le_of_nonneg_of_nonpos <;> omega
  · rw [← Int.neg_mul]; apply Int.mul_le_mul_of_le_of_le_of_nonneg_of_nonpos <;> omega
  · have : 0 < x * y := by apply Int.mul_pos_of_neg_of_neg <;> omega
    norm_cast
    omega

/-! ## pow -/

theorem natAbs_pow_two (a : Int) : (natAbs a : Int) ^ 2 = a ^ 2 := by
  simp [Int.pow_succ]

end Int
