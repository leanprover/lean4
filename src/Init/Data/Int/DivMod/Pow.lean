/-
Copyright (c) 2025 Lean FRO, LLC All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
import Init.ByCases
import Init.Data.Int.DivMod.Bootstrap
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.Lemmas
import Init.Data.Int.Pow
import Init.RCases

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
  obtain ⟨c, rfl⟩ := hab
  by_cases b = 0
  · by_cases n = 0 <;> simp [*, Int.zero_pow]
  · simp [Int.mul_pow, Int.pow_ne_zero, *]

theorem tdiv_pow {a b : Int} {n : Nat} (hab : b ∣ a) :
    (a.tdiv b) ^ n = (a ^ n).tdiv (b ^ n) := by
  rw [Int.tdiv_eq_ediv_of_dvd hab, ediv_pow hab, Int.tdiv_eq_ediv_of_dvd (dvd_pow hab)]

theorem fdiv_pow {a b : Int} {n : Nat} (hab : b ∣ a) :
    (a.fdiv b) ^ n = (a ^ n).fdiv (b ^ n) := by
  rw [Int.fdiv_eq_ediv_of_dvd hab, ediv_pow hab, Int.fdiv_eq_ediv_of_dvd (dvd_pow hab)]
