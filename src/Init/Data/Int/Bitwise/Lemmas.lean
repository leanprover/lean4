/-
Copyright (c) 2023 Siddharth Bhat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat, Jeremy Avigad
-/
prelude
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Int.Bitwise

namespace Int

theorem shiftRight_eq (n : Int) (s : Nat) : n >>> s = Int.shiftRight n s := rfl
@[simp]
theorem natCast_shiftRight (n s : Nat) : (n : Int) >>> s = n >>> s := rfl

@[simp]
theorem negSucc_shiftRight (m n : Nat) :
    -[m+1] >>> n = -[m >>>n +1] := rfl

/-- Equation theorem for 'Int.sub' when the arguments are `.ofNat` and
  the result is known to be negative. -/
private theorem toNat_sub_toNat_eq_negSucc_ofLt {n m : Nat} (hlt : n < m) :
  (n : Int) - (m : Int) = (Int.negSucc (m - 1 - n)) := by
  rw [Int.negSucc_eq] -- TODO: consider adding this to omega cleanup set.
  omega

/-- shiftRight of a subtraction is evaluated when
  the result of the subtraction is negative. -/
theorem toNat_sub_toNat_shiftRight_eq_ofLt {m n i: Nat} (h : m < n) :
  ((m : Int) - (n : Int)) >>> i = -[((n - 1 - m) >>> i) +1] := by
    rw [toNat_sub_toNat_eq_negSucc_ofLt (by omega)]
    rw [negSucc_shiftRight]

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

end Int
