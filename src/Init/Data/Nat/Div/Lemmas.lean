/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Omega
import Init.Data.Nat.Lemmas

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
theorem div_eq_iff (h : 0 < k) : x / k = y ↔ x ≤ y * k + k - 1 ∧ y * k ≤ x := by
  rw [Nat.eq_iff_le_and_ge, le_div_iff_mul_le h, Nat.div_le_iff_le_mul h]

theorem lt_of_div_eq_zero (h : 0 < k) (h' : x / k = 0) : x < k := by
  rw [div_eq_iff h] at h'
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

end Nat
