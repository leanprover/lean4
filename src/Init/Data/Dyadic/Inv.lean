/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Dyadic.Basic
import Init.Data.Rat.Lemmas

/-!
# Inversion for dyadic numbers
-/

@[expose] public section

namespace Dyadic

/--
Inverts a dyadic number at a given (maximum) precision.
Returns the greatest dyadic number with precision at most `prec` which is less than or equal to `1/x`.
For `x = 0`, returns `0`.
-/
def invAtPrec (x : Dyadic) (prec : Int) : Dyadic :=
  match x with
  | .zero => .zero
  | _ => x.toRat.inv.toDyadic prec

/-- For a positive dyadic `x`, `invAtPrec x prec * x ≤ 1`. -/
theorem invAtPrec_mul_le_one {x : Dyadic} (hx : 0 < x) (prec : Int) :
    invAtPrec x prec * x ≤ 1 := by
  rw [← toRat_le_toRat_iff]
  rw [toRat_mul]
  rw [show (1 : Dyadic).toRat = (1 : Rat) from rfl]
  unfold invAtPrec
  cases x with
  | zero =>
    exfalso
    contradiction
  | ofOdd n k hn =>
    simp only
    have h_le : ((ofOdd n k hn).toRat.inv.toDyadic prec).toRat ≤ (ofOdd n k hn).toRat.inv := Rat.toRat_toDyadic_le
    have h_pos : 0 ≤ (ofOdd n k hn).toRat := by
      rw [← toRat_lt_toRat_iff, toRat_zero] at hx
      exact Rat.le_of_lt hx
    calc ((ofOdd n k hn).toRat.inv.toDyadic prec).toRat * (ofOdd n k hn).toRat
        ≤ (ofOdd n k hn).toRat.inv * (ofOdd n k hn).toRat := Rat.mul_le_mul_of_nonneg_right h_le h_pos
      _ = 1 := by
        apply Rat.inv_mul_cancel
        rw [← toRat_lt_toRat_iff, toRat_zero] at hx
        exact Rat.ne_of_gt hx

/-- For a positive dyadic `x`, `1 < (invAtPrec x prec + 2^(-prec)) * x`. -/
theorem one_lt_invAtPrec_add_inc_mul {x : Dyadic} (hx : 0 < x) (prec : Int) :
    1 < (invAtPrec x prec + ofIntWithPrec 1 prec) * x := by
  rw [← toRat_lt_toRat_iff]
  rw [toRat_mul]
  rw [show (1 : Dyadic).toRat = (1 : Rat) from rfl]
  unfold invAtPrec
  cases x with
  | zero =>
    exfalso
    contradiction
  | ofOdd n k hn =>
    simp only
    have h_le : (ofOdd n k hn).toRat.inv < ((ofOdd n k hn).toRat.inv.toDyadic prec + ofIntWithPrec 1 prec).toRat :=
      Rat.lt_toRat_toDyadic_add
    have h_pos : 0 < (ofOdd n k hn).toRat := by
      rwa [← toRat_lt_toRat_iff, toRat_zero] at hx
    calc
      1 = (ofOdd n k hn).toRat.inv * (ofOdd n k hn).toRat := by
        symm
        apply Rat.inv_mul_cancel
        rw [← toRat_lt_toRat_iff, toRat_zero] at hx
        exact Rat.ne_of_gt hx
      _ < ((ofOdd n k hn).toRat.inv.toDyadic prec + ofIntWithPrec 1 prec).toRat * (ofOdd n k hn).toRat :=
           Rat.mul_lt_mul_of_pos_right h_le h_pos

-- TODO: `invAtPrec` is the unique dyadic with the given precision satisfying the two inequalities above.

end Dyadic
