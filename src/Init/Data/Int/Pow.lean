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

theorem pow_le_pow_of_le_left {n m : Nat} (h : n ≤ m) : ∀ (i : Nat), n^i ≤ m^i
  | 0      => Nat.le_refl _
  | i + 1 => Nat.mul_le_mul (pow_le_pow_of_le_left h i) h

theorem pow_le_pow_of_le_right {n : Nat} (hx : n > 0) {i : Nat} : ∀ {j}, i ≤ j → n^i ≤ n^j
  | 0,      h =>
    have : i = 0 := Nat.eq_zero_of_le_zero h
    this.symm ▸ Nat.le_refl _
  | j + 1, h =>
    match Nat.le_or_eq_of_le_succ h with
    | Or.inl h => show n^i ≤ n^j * n from
      have : n^i * 1 ≤ n^j * n := Nat.mul_le_mul (pow_le_pow_of_le_right hx h) hx
      Nat.mul_one (n^i) ▸ this
    | Or.inr h =>
      h.symm ▸ Nat.le_refl _

theorem pos_pow_of_pos {n : Nat} (m : Nat) (h : 0 < n) : 0 < n^m :=
  pow_le_pow_of_le_right h (Nat.zero_le _)

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
