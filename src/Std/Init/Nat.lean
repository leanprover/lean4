/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.Nat.Bitwise.Lemmas
import Init.RCases

namespace Nat

theorem lt_of_eq_of_lt {n m k : Nat} : n = m → m < k → n < k :=
  fun h₁ h₂ => h₁ ▸ h₂

theorem le_of_testBit {n m : Nat} (h : ∀ i, n.testBit i = true → m.testBit i = true) : n ≤ m := by
  induction n using Nat.div2Induction generalizing m
  next n ih =>
  have : n / 2 ≤ m / 2 := by
    rcases n with (_|n)
    · simp
    · apply ih (Nat.succ_pos _)
      intro i
      simpa using h (i + 1)
  rw [← Nat.div_add_mod n 2, ← Nat.div_add_mod m 2]
  cases hn : n.testBit 0
  · have hn2 : n % 2 = 0 := by simp [Nat.testBit_zero] at hn; omega
    rw [hn2, Nat.add_zero]
    exact Nat.le_trans (Nat.mul_le_mul_left _ this) (Nat.le_add_right _ _)
  · have hn2 : n % 2 = 1 := by simp [Nat.testBit_zero] at hn; omega
    have hm := h _ hn
    have hm2 : m % 2 = 1 := by simp [Nat.testBit_zero] at hm; omega
    rw [hn2, hm2]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ this) _

theorem and_le_left {n m : Nat} : n &&& m ≤ n :=
  le_of_testBit (by simpa using fun i x _ => x)

theorem and_le_right {n m : Nat} : n &&& m ≤ m :=
  le_of_testBit (by simp)

theorem toNat_toUSize {a : Nat} (h : a < USize.size) : a.toUSize.toNat = a :=
  Nat.mod_eq_of_lt h

theorem toUSize_one : (1 : Nat).toUSize = 1 := rfl

end Nat
