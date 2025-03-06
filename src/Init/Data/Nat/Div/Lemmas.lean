/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Omega
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

/-!
# Further lemmas about `Nat.div` and `Nat.mod`, with the convenience of having `omega` available.
-/

namespace Nat

theorem lt_div_iff_mul_lt (h : 0 < k) : x < y / k ↔ x * k < y - (k - 1) := by
  have t := le_div_iff_mul_le h (x := x + 1) (y := y)
  rw [succ_le, add_one_mul] at t
  have s : k = k - 1 + 1 := by omega
  conv at t => rhs; lhs; rhs; rw [s]
  rw [← Nat.add_assoc, succ_le, add_lt_iff_lt_sub_right] at t
  exact t

theorem div_le_iff_le_mul (h : 0 < k) : x / k ≤ y ↔ x ≤ y * k + k - 1 := by
  rw [le_iff_lt_add_one, Nat.div_lt_iff_lt_mul h, Nat.add_one_mul]
  omega

-- TODO: reprove `div_eq_of_lt_le` in terms of this:
protected theorem div_eq_iff (h : 0 < k) : x / k = y ↔ y * k ≤ x ∧ x ≤ y * k + k - 1 := by
  rw [Nat.eq_iff_le_and_ge, and_comm, le_div_iff_mul_le h, Nat.div_le_iff_le_mul h]

theorem lt_of_div_eq_zero (h : 0 < k) (h' : x / k = 0) : x < k := by
  rw [Nat.div_eq_iff h] at h'
  omega

theorem div_eq_zero_iff_lt (h : 0 < k) : x / k = 0 ↔ x < k :=
  ⟨lt_of_div_eq_zero h, fun h' => Nat.div_eq_of_lt h'⟩

theorem div_mul_self_eq_mod_sub_self {x k : Nat} : (x / k) * k = x - (x % k) := by
  have := mod_eq_sub_div_mul (x := x) (k := k)
  have := div_mul_le_self x k
  omega

theorem mul_div_self_eq_mod_sub_self {x k : Nat} : k * (x / k) = x - (x % k) := by
  rw [Nat.mul_comm, div_mul_self_eq_mod_sub_self]

theorem lt_div_mul_self (h : 0 < k) (w : k ≤ x) : x - k < x / k * k := by
  rw [div_mul_self_eq_mod_sub_self]
  have : x % k < k := mod_lt x h
  omega

theorem div_pos (hba : b ≤ a) (hb : 0 < b) : 0 < a / b := by
  cases b
  · contradiction
  · simp [Nat.pos_iff_ne_zero, div_eq_zero_iff_lt, hba]

theorem div_le_div_left (hcb : c ≤ b) (hc : 0 < c) : a / b ≤ a / c :=
  (Nat.le_div_iff_mul_le hc).2 <|
    Nat.le_trans (Nat.mul_le_mul_left _ hcb) (Nat.div_mul_le_self a b)

theorem div_add_le_right {z : Nat} (h : 0 < z) (x y : Nat) :
    x / (y + z) ≤ x / z :=
  div_le_div_left (Nat.le_add_left z y) h

theorem succ_div_of_dvd {a b : Nat} (h : b ∣ a + 1) :
    (a + 1) / b = a / b + 1 := by
  replace h := mod_eq_zero_of_dvd h
  cases b with
  | zero => simp at h
  | succ b =>
    by_cases h' : b ≤ a
    · rw [Nat.div_eq]
      simp only [zero_lt_succ, Nat.add_le_add_iff_right, h', and_self, ↓reduceIte,
        Nat.reduceSubDiff, Nat.add_right_cancel_iff]
      obtain ⟨_|k, h⟩ := Nat.dvd_of_mod_eq_zero h
      · simp at h
      · simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one, ← Nat.add_assoc,
          Nat.add_right_cancel_iff] at h
        subst h
        rw [Nat.add_sub_cancel, ← Nat.add_one_mul, mul_div_right _ (zero_lt_succ _), Nat.add_comm,
          Nat.add_mul_div_left _ _ (zero_lt_succ _), Nat.self_eq_add_left, div_eq_of_lt le.refl]
    · simp only [Nat.not_le] at h'
      replace h' : a + 1 < b + 1 := Nat.add_lt_add_right h' 1
      rw [Nat.mod_eq_of_lt h'] at h
      simp at h

theorem succ_div_of_mod_eq_zero {a b : Nat} (h : (a + 1) % b = 0) :
    (a + 1) / b = a / b + 1 := by
  rw [succ_div_of_dvd (by rwa [dvd_iff_mod_eq_zero])]

theorem succ_div_of_not_dvd {a b : Nat} (h : ¬ b ∣ a + 1) :
    (a + 1) / b = a / b := by
  replace h := mt dvd_of_mod_eq_zero h
  cases b with
  | zero => simp
  | succ b =>
    rw [eq_comm, Nat.div_eq_iff (by simp)]
    constructor
    · rw [Nat.div_mul_self_eq_mod_sub_self]
      omega
    · rw [Nat.div_mul_self_eq_mod_sub_self]
      have : (a + 1) % (b + 1) < b + 1 := Nat.mod_lt _ (by simp)
      omega

theorem succ_div_of_mod_ne_zero {a b : Nat} (h : (a + 1) % b ≠ 0) :
    (a + 1) / b = a / b := by
  rw [succ_div_of_not_dvd (by rwa [dvd_iff_mod_eq_zero])]

protected theorem succ_div {a b : Nat} : (a + 1) / b = a / b + if b ∣ a + 1 then 1 else 0 := by
  split <;> rename_i h
  · simp [succ_div_of_dvd h]
  · simp [succ_div_of_not_dvd h]

protected theorem add_div {a b c : Nat} (h : 0 < c) :
    (a + b) / c = a / c + b / c + if c ≤ a % c + b % c then 1 else 0 := by
  conv => lhs; rw [← Nat.div_add_mod a c]
  rw [Nat.add_assoc, mul_add_div h]
  conv => lhs; rw [← Nat.div_add_mod b c]
  rw [Nat.add_comm (a % c), Nat.add_assoc, mul_add_div h, ← Nat.add_assoc, Nat.add_comm (b % c)]
  congr
  rw [Nat.div_eq_iff h]
  constructor
  · split <;> rename_i h
    · simpa using h
    · simp
  · have := mod_lt a h
    have := mod_lt b h
    split <;> · simp; omega

end Nat
