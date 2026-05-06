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
# Inversion and division for dyadic numbers
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

/--
Divides two dyadic numbers at a given (maximum) precision.
Returns the greatest dyadic number with precision at most `prec` which is less than or equal
to `a/b`. For `b = 0`, returns `0`.
-/
def divAtPrec (a b : Dyadic) (prec : Int) : Dyadic :=
  match b with
  | .zero => .zero
  | _ => (a.toRat / b.toRat).toDyadic prec

/-- For a positive dyadic `b`, `divAtPrec a b prec * b ≤ a`. -/
theorem divAtPrec_mul_le {a b : Dyadic} (hb : 0 < b) (prec : Int) :
    divAtPrec a b prec * b ≤ a := by
  rw [← toRat_le_toRat_iff]
  rw [toRat_mul]
  unfold divAtPrec
  cases b with
  | zero =>
    exfalso
    contradiction
  | ofOdd n k hn =>
    simp only
    have h_le : ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec).toRat ≤
        a.toRat / (ofOdd n k hn).toRat := Rat.toRat_toDyadic_le
    have h_pos : 0 ≤ (ofOdd n k hn).toRat := by
      rw [← toRat_lt_toRat_iff, toRat_zero] at hb
      exact Rat.le_of_lt hb
    calc ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec).toRat * (ofOdd n k hn).toRat
        ≤ a.toRat / (ofOdd n k hn).toRat * (ofOdd n k hn).toRat :=
            Rat.mul_le_mul_of_nonneg_right h_le h_pos
      _ = a.toRat := by
        apply Rat.div_mul_cancel
        rw [← toRat_lt_toRat_iff, toRat_zero] at hb
        exact Rat.ne_of_gt hb

/-- For a positive dyadic `b`, `a < (divAtPrec a b prec + 2^(-prec)) * b`. -/
theorem lt_divAtPrec_add_inc_mul {a b : Dyadic} (hb : 0 < b) (prec : Int) :
    a < (divAtPrec a b prec + ofIntWithPrec 1 prec) * b := by
  rw [← toRat_lt_toRat_iff]
  rw [toRat_mul]
  unfold divAtPrec
  cases b with
  | zero =>
    exfalso
    contradiction
  | ofOdd n k hn =>
    simp only
    have h_lt : a.toRat / (ofOdd n k hn).toRat <
        ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec + ofIntWithPrec 1 prec).toRat :=
      Rat.lt_toRat_toDyadic_add
    have h_pos : 0 < (ofOdd n k hn).toRat := by
      rwa [← toRat_lt_toRat_iff, toRat_zero] at hb
    calc
      a.toRat = a.toRat / (ofOdd n k hn).toRat * (ofOdd n k hn).toRat := by
        symm
        apply Rat.div_mul_cancel
        rw [← toRat_lt_toRat_iff, toRat_zero] at hb
        exact Rat.ne_of_gt hb
      _ < ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec + ofIntWithPrec 1 prec).toRat *
            (ofOdd n k hn).toRat :=
          Rat.mul_lt_mul_of_pos_right h_lt h_pos

-- TODO: `divAtPrec` is the unique dyadic with the given precision satisfying the two inequalities above.

end Dyadic
