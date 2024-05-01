/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
prelude
import Init.Data.Nat.Gcd
import Init.Data.Nat.Lemmas

namespace Nat

/-- The least common multiple of `m` and `n`, defined using `gcd`. -/
def lcm (m n : Nat) : Nat := m * n / gcd m n

theorem lcm_comm (m n : Nat) : lcm m n = lcm n m := by
  rw [lcm, lcm, Nat.mul_comm n m, gcd_comm n m]
instance : Std.Commutative lcm := ⟨lcm_comm⟩

@[simp] theorem lcm_zero_left (m : Nat) : lcm 0 m = 0 := by simp [lcm]

@[simp] theorem lcm_zero_right (m : Nat) : lcm m 0 = 0 := by simp [lcm]

@[simp] theorem lcm_one_left (m : Nat) : lcm 1 m = m := by simp [lcm]

@[simp] theorem lcm_one_right (m : Nat) : lcm m 1 = m := by simp [lcm]
instance : Std.LawfulIdentity lcm 1 where
  left_id := lcm_one_left
  right_id := lcm_one_right

@[simp] theorem lcm_self (m : Nat) : lcm m m = m := by
  match eq_zero_or_pos m with
  | .inl h => rw [h, lcm_zero_left]
  | .inr h => simp [lcm, Nat.mul_div_cancel _ h]
instance : Std.IdempotentOp lcm := ⟨lcm_self⟩

theorem dvd_lcm_left (m n : Nat) : m ∣ lcm m n :=
  ⟨n / gcd m n, by rw [← Nat.mul_div_assoc m (Nat.gcd_dvd_right m n)]; rfl⟩

theorem dvd_lcm_right (m n : Nat) : n ∣ lcm m n := lcm_comm n m ▸ dvd_lcm_left n m

theorem gcd_mul_lcm (m n : Nat) : gcd m n * lcm m n = m * n := by
  rw [lcm, Nat.mul_div_cancel' (Nat.dvd_trans (gcd_dvd_left m n) (Nat.dvd_mul_right m n))]

theorem lcm_dvd {m n k : Nat} (H1 : m ∣ k) (H2 : n ∣ k) : lcm m n ∣ k := by
  match eq_zero_or_pos k with
  | .inl h => rw [h]; exact Nat.dvd_zero _
  | .inr kpos =>
    apply Nat.dvd_of_mul_dvd_mul_left (gcd_pos_of_pos_left n (pos_of_dvd_of_pos H1 kpos))
    rw [gcd_mul_lcm, ← gcd_mul_right, Nat.mul_comm n k]
    exact dvd_gcd (Nat.mul_dvd_mul_left _ H2) (Nat.mul_dvd_mul_right H1 _)

theorem lcm_assoc (m n k : Nat) : lcm (lcm m n) k = lcm m (lcm n k) :=
Nat.dvd_antisymm
  (lcm_dvd
    (lcm_dvd (dvd_lcm_left m (lcm n k))
      (Nat.dvd_trans (dvd_lcm_left n k) (dvd_lcm_right m (lcm n k))))
    (Nat.dvd_trans (dvd_lcm_right n k) (dvd_lcm_right m (lcm n k))))
  (lcm_dvd
    (Nat.dvd_trans (dvd_lcm_left m n) (dvd_lcm_left (lcm m n) k))
    (lcm_dvd (Nat.dvd_trans (dvd_lcm_right m n) (dvd_lcm_left (lcm m n) k))
      (dvd_lcm_right (lcm m n) k)))
instance : Std.Associative lcm := ⟨lcm_assoc⟩

theorem lcm_ne_zero (hm : m ≠ 0) (hn : n ≠ 0) : lcm m n ≠ 0 := by
  intro h
  have h1 := gcd_mul_lcm m n
  rw [h, Nat.mul_zero] at h1
  match mul_eq_zero.1 h1.symm with
  | .inl hm1 => exact hm hm1
  | .inr hn1 => exact hn hn1

end Nat
