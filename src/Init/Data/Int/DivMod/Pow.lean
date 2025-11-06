/-
Copyright (c) 2025 Lean FRO, LLC All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Init.Data.Int.DivMod.Lemmas
public import Init.Data.Int.Pow

/-!
# Lemmas about divisibility of powers
-/

namespace Int

theorem dvd_pow {a b : Int} {n : Nat} (hab : b ∣ a) : b ^ n ∣ a ^ n := by
  rcases hab with ⟨c, rfl⟩
  rw [Int.mul_pow]
  exact Int.dvd_mul_right (b ^ n) (c ^ n)

theorem ediv_pow {a b : Int} {n : Nat} (hab : b ∣ a) :
    (a / b) ^ n = a ^ n / b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have w : b ^ n ∣ a ^ n := dvd_pow hab
    have h : b ^ n ∣ a / b * a ^ n := Int.dvd_mul_of_dvd_right w
    rw [Int.pow_succ, ih, Int.pow_succ, Int.pow_succ, Int.mul_comm _ b,
      Int.ediv_mul, Int.mul_ediv_assoc _ hab, Int.mul_comm (a ^ n),
      Int.mul_ediv_assoc _ w, if_neg, Int.add_zero, Int.mul_comm]
    simp [h]

theorem tdiv_pow {a b : Int} {n : Nat} (hab : b ∣ a) :
    (a.tdiv b) ^ n = (a ^ n).tdiv (b ^ n) := by
  rw [Int.tdiv_eq_ediv_of_dvd hab, ediv_pow hab, Int.tdiv_eq_ediv_of_dvd (dvd_pow hab)]

theorem fdiv_pow {a b : Int} {n : Nat} (hab : b ∣ a) :
    (a.fdiv b) ^ n = (a ^ n).fdiv (b ^ n) := by
  rw [Int.fdiv_eq_ediv_of_dvd hab, ediv_pow hab, Int.fdiv_eq_ediv_of_dvd (dvd_pow hab)]
