/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Deniz Aydin, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.Int.Lemmas
import Init.Data.Nat.Lemmas

namespace Int

/-! # pow -/

protected theorem pow_zero (b : Int) : b^0 = 1 := rfl

protected theorem pow_succ (b : Int) (e : Nat) : b ^ (e+1) = (b ^ e) * b := rfl
protected theorem pow_succ' (b : Int) (e : Nat) : b ^ (e+1) = b * (b ^ e) := by
  rw [Int.mul_comm, Int.pow_succ]

@[deprecated Nat.pow_le_pow_left (since := "2025-02-17")]
abbrev pow_le_pow_of_le_left := @Nat.pow_le_pow_left

@[deprecated Nat.pow_le_pow_right (since := "2025-02-17")]
abbrev pow_le_pow_of_le_right := @Nat.pow_le_pow_right

@[deprecated Nat.pow_pos (since := "2025-02-17")]
abbrev pos_pow_of_pos := @Nat.pow_pos

@[norm_cast]
theorem natCast_pow (b n : Nat) : ((b^n : Nat) : Int) = (b : Int) ^ n := by
  match n with
  | 0 => rfl
  | n + 1 =>
    simp only [Nat.pow_succ, Int.pow_succ, natCast_mul, natCast_pow _ n]

@[simp]
protected theorem two_pow_pred_sub_two_pow {w : Nat} (h : 0 < w) :
    ((2 ^ (w - 1) : Nat) - (2 ^ w : Nat) : Int) = - ((2 ^ (w - 1) : Nat) : Int) := by
  rw [← Nat.two_pow_pred_add_two_pow_pred h]
  omega

@[simp]
protected theorem two_pow_pred_sub_two_pow' {w : Nat} (h : 0 < w) :
    (2 : Int) ^ (w - 1) - (2 : Int) ^ w = - (2 : Int) ^ (w - 1) := by
  norm_cast
  rw [← Nat.two_pow_pred_add_two_pow_pred h]
  simp [h]

end Int
