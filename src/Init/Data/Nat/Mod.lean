/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Omega

/-!
# Further results about `mod`.

This file proves some results about `mod` that are useful for bitblasting,
in particular
`Nat.mod_mul : x % (a * b) = x % a + a * (x / a % b)`
and its corollary
`Nat.mod_pow_succ : x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b)`.

It contains the necessary preliminary results relating order and `*` and `/`,
which should probably be moved to their own file.
-/

namespace Nat

@[simp] protected theorem mul_lt_mul_left (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega

@[simp] protected theorem mul_lt_mul_right (a0 : 0 < a) : b * a < c * a ↔ b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a, Nat.mul_lt_mul_left a0]

protected theorem lt_of_mul_lt_mul_left {a b c : Nat} (h : a * b < a * c) : b < c := by
  cases a <;> simp_all

protected theorem lt_of_mul_lt_mul_right {a b c : Nat} (h : b * a < c * a) : b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a] at h
  exact Nat.lt_of_mul_lt_mul_left h

protected theorem div_lt_of_lt_mul {m n k : Nat} (h : m < n * k) : m / n < k :=
  Nat.lt_of_mul_lt_mul_left <|
    calc
      n * (m / n) ≤ m % n + n * (m / n) := Nat.le_add_left _ _
      _ = m := mod_add_div _ _
      _ < n * k := h

theorem mod_mul_right_div_self (m n k : Nat) : m % (n * k) / n = m / n % k := by
  rcases Nat.eq_zero_or_pos n with (rfl | hn); simp [mod_zero]
  rcases Nat.eq_zero_or_pos k with (rfl | hk); simp [mod_zero]
  conv => rhs; rw [← mod_add_div m (n * k)]
  rw [Nat.mul_assoc, add_mul_div_left _ _ hn, add_mul_mod_self_left,
    mod_eq_of_lt (Nat.div_lt_of_lt_mul (mod_lt _ (Nat.mul_pos hn hk)))]

theorem mod_mul_left_div_self (m n k : Nat) : m % (k * n) / n = m / n % k := by
  rw [Nat.mul_comm k n, mod_mul_right_div_self]

@[simp]
theorem mod_mul_right_mod (a b c : Nat) : a % (b * c) % b = a % b :=
  Nat.mod_mod_of_dvd a (Nat.dvd_mul_right b c)

@[simp]
theorem mod_mul_left_mod (a b c : Nat) : a % (b * c) % c = a % c :=
  Nat.mod_mod_of_dvd a (Nat.mul_comm _ _ ▸ Nat.dvd_mul_left c b)

theorem mod_mul {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]

theorem mod_pow_succ {x b k : Nat} :
    x % b ^ (k + 1) = x % b ^ k + b ^ k * ((x / b ^ k) % b) := by
  rw [Nat.pow_succ, Nat.mod_mul]

@[simp] theorem two_pow_mod_two_eq_zero {n : Nat} : 2 ^ n % 2 = 0 ↔ 0 < n := by
  cases n <;> simp [Nat.pow_succ]

@[simp] theorem two_pow_mod_two_eq_one {n : Nat} : 2 ^ n % 2 = 1 ↔ n = 0 := by
  cases n <;> simp [Nat.pow_succ]

end Nat
