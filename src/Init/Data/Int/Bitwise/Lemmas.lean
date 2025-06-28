/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat, Jeremy Avigad
-/
module

prelude
public import Init.Data.Nat.Bitwise.Lemmas
public import all Init.Data.Int.Bitwise.Basic
public import Init.Data.Int.DivMod.Lemmas

public section

namespace Int

theorem shiftRight_eq (n : Int) (s : Nat) : n >>> s = Int.shiftRight n s := rfl

@[simp]
theorem natCast_shiftRight (n s : Nat) : (n : Int) >>> s = n >>> s := rfl

@[simp]
theorem negSucc_shiftRight (m n : Nat) :
    -[m+1] >>> n = -[m >>>n +1] := rfl

@[grind _=_]
theorem shiftRight_add (i : Int) (m n : Nat) :
    i >>> (m + n) = i >>> m >>> n := by
  simp only [shiftRight_eq, Int.shiftRight]
  cases i <;> simp [Nat.shiftRight_add]

theorem shiftRight_eq_div_pow (m : Int) (n : Nat) :
    m >>> n = m / ((2 ^ n) : Nat) := by
  simp only [shiftRight_eq, Int.shiftRight, Nat.shiftRight_eq_div_pow]
  split
  · simp
  · rw [negSucc_ediv _ (by norm_cast; exact Nat.pow_pos (Nat.zero_lt_two))]
    rfl

@[simp]
theorem zero_shiftRight (n : Nat) : (0 : Int) >>> n = 0 := by
  simp [Int.shiftRight_eq_div_pow]

@[simp]
theorem shiftRight_zero (n : Int) : n >>> 0 = n := by
  simp [Int.shiftRight_eq_div_pow]

theorem le_shiftRight_of_nonpos {n : Int} {s : Nat} (h : n ≤ 0) : n ≤ n >>> s := by
  simp only [Int.shiftRight_eq, Int.shiftRight, Int.ofNat_eq_coe]
  split
  case _ _ _ m =>
    simp only [ofNat_eq_coe] at h
    by_cases hm : m = 0
    · simp [hm]
    · omega
  case _ _ _ m =>
    by_cases hm : m = 0
    · simp [hm]
    · have := Nat.shiftRight_le m s
      omega

theorem shiftRight_le_of_nonneg {n : Int} {s : Nat} (h : 0 ≤ n) : n >>> s ≤ n := by
  simp only [Int.shiftRight_eq, Int.shiftRight, Int.ofNat_eq_coe]
  split
  case _ _ _ m =>
    simp only [Int.ofNat_eq_coe] at h
    by_cases hm : m = 0
    · simp [hm]
    · have := Nat.shiftRight_le m s
      simp
      omega
  case _ _ _ m =>
    omega

theorem le_shiftRight_of_nonneg {n : Int} {s : Nat} (h : 0 ≤ n) : 0 ≤ (n >>> s) := by
  rw [Int.shiftRight_eq_div_pow]
  by_cases h' : s = 0
  · simp [h', h]
  · have := @Nat.pow_pos 2 s (by omega)
    have := @Int.ediv_nonneg n (2^s) h (by norm_cast at *; omega)
    norm_cast at *

theorem shiftRight_le_of_nonpos {n : Int} {s : Nat} (h : n ≤ 0) : (n >>> s) ≤ 0 := by
  rw [Int.shiftRight_eq_div_pow]
  by_cases h' : s = 0
  · simp [h', h]
  · have : 1 < 2 ^ s := Nat.one_lt_two_pow (by omega)
    have rl : n / 2 ^ s ≤ 0 := Int.ediv_nonpos_of_nonpos_of_neg (by omega) (by norm_cast at *; omega)
    norm_cast at *

end Int
