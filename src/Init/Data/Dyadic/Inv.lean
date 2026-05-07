/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Dyadic.Basic
import Init.Data.Int.Order
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
  have hxr : (0 : Rat) < x.toRat := by rwa [← toRat_lt_toRat_iff, toRat_zero] at hx
  rw [← toRat_le_toRat_iff, toRat_mul, show (1 : Dyadic).toRat = (1 : Rat) from rfl]
  unfold invAtPrec
  cases x with
  | zero => exfalso; contradiction
  | ofOdd n k hn =>
    simp only
    calc ((ofOdd n k hn).toRat.inv.toDyadic prec).toRat * (ofOdd n k hn).toRat
        ≤ (ofOdd n k hn).toRat.inv * (ofOdd n k hn).toRat :=
          Rat.mul_le_mul_of_nonneg_right Rat.toRat_toDyadic_le (Rat.le_of_lt hxr)
      _ = 1 := Rat.inv_mul_cancel _ (Rat.ne_of_gt hxr)

/-- For a positive dyadic `x`, `1 < (invAtPrec x prec + 2^(-prec)) * x`. -/
theorem one_lt_invAtPrec_add_inc_mul {x : Dyadic} (hx : 0 < x) (prec : Int) :
    1 < (invAtPrec x prec + ofIntWithPrec 1 prec) * x := by
  have hxr : (0 : Rat) < x.toRat := by rwa [← toRat_lt_toRat_iff, toRat_zero] at hx
  rw [← toRat_lt_toRat_iff, toRat_mul, show (1 : Dyadic).toRat = (1 : Rat) from rfl]
  unfold invAtPrec
  cases x with
  | zero => exfalso; contradiction
  | ofOdd n k hn =>
    simp only
    calc (1 : Rat)
        = (ofOdd n k hn).toRat.inv * (ofOdd n k hn).toRat :=
          (Rat.inv_mul_cancel _ (Rat.ne_of_gt hxr)).symm
      _ < ((ofOdd n k hn).toRat.inv.toDyadic prec + ofIntWithPrec 1 prec).toRat
            * (ofOdd n k hn).toRat :=
          Rat.mul_lt_mul_of_pos_right Rat.lt_toRat_toDyadic_add hxr

/--
If `y : Dyadic` has precision at most `prec` and a rational `q` lies in the half-open
interval `[y.toRat, y.toRat + 2 ^ (-prec))`, then `y` is the floor of `q` at precision
`prec`, i.e. `y = q.toDyadic prec`.
-/
theorem eq_toDyadic_of_precision_le {q : Rat} {y : Dyadic} {prec : Int}
    (hp : y.precision ≤ some prec)
    (h1 : y.toRat ≤ q) (h2 : q < y.toRat + (2 : Rat) ^ (-prec)) :
    y = q.toDyadic prec := by
  have h2pos : (0 : Rat) < (2 : Rat) ^ prec := Rat.zpow_pos (by decide)
  have h2ne : ((2 : Rat) ^ prec) ≠ 0 := Rat.ne_of_gt h2pos
  -- Canonical form: `y.toRat = ((y.toRat * 2 ^ prec).floor : Rat) / 2 ^ prec`.
  have hcan : y.toRat = (((y.toRat * 2 ^ prec).floor : Int) : Rat) / 2 ^ prec := by
    have h := congrArg Dyadic.toRat
      (show y.toRat.toDyadic prec = y by rw [toDyadic_toRat, roundDown_eq_self_of_le hp])
    rwa [Rat.toRat_toDyadic, eq_comm] at h
  -- Multiplied form: `y.toRat * 2 ^ prec` equals its own floor cast back.
  have hL : y.toRat * (2 : Rat) ^ prec = (((y.toRat * 2 ^ prec).floor : Int) : Rat) := by
    have := congrArg (· * (2 : Rat) ^ prec) hcan
    simp only at this
    rwa [Rat.div_mul_cancel h2ne] at this
  -- Multiply `h1`, `h2` by `2 ^ prec`.
  have h1' : y.toRat * 2 ^ prec ≤ q * 2 ^ prec :=
    Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt h2pos)
  have h2' : q * 2 ^ prec < y.toRat * 2 ^ prec + 1 := by
    have := Rat.mul_lt_mul_of_pos_right h2 h2pos
    rwa [Rat.add_mul, Rat.zpow_neg, Rat.inv_mul_cancel _ h2ne] at this
  -- Identify floors.
  have hQfloor : (q * 2 ^ prec).floor = (y.toRat * 2 ^ prec).floor := by
    apply Int.le_antisymm
    · rw [← Int.lt_add_one_iff, Rat.floor_lt_iff,
          Rat.intCast_add, Rat.intCast_one, ← hL]
      exact h2'
    · rw [Rat.le_floor_iff, ← hL]
      exact h1'
  -- Conclude.
  rw [← toRat_inj, Rat.toRat_toDyadic, hQfloor]
  exact hcan

/--
`invAtPrec x prec` is the unique dyadic with precision at most `prec` satisfying
both `_ * x ≤ 1` and `1 < (_ + ofIntWithPrec 1 prec) * x`, for `0 < x`.
-/
theorem eq_invAtPrec {x : Dyadic} (hx : 0 < x) {prec : Int} {y : Dyadic}
    (hp : y.precision ≤ some prec) (h1 : y * x ≤ 1)
    (h2 : 1 < (y + ofIntWithPrec 1 prec) * x) :
    y = invAtPrec x prec := by
  have hxr : (0 : Rat) < x.toRat := by rwa [← toRat_lt_toRat_iff, toRat_zero] at hx
  have hxne : x.toRat ≠ 0 := Rat.ne_of_gt hxr
  rw [← toRat_le_toRat_iff, toRat_mul, show (1 : Dyadic).toRat = (1 : Rat) from rfl] at h1
  rw [← toRat_lt_toRat_iff, toRat_mul, toRat_add, toRat_ofIntWithPrec_eq_mul_two_pow,
      show (1 : Dyadic).toRat = (1 : Rat) from rfl, Rat.intCast_one, Rat.one_mul] at h2
  have hinv_mul : x.toRat.inv * x.toRat = 1 := Rat.inv_mul_cancel _ hxne
  have hyle : y.toRat ≤ x.toRat.inv :=
    Rat.le_of_mul_le_mul_right
      (calc y.toRat * x.toRat
          ≤ 1 := h1
        _ = x.toRat.inv * x.toRat := hinv_mul.symm) hxr
  have hltinv : x.toRat.inv < y.toRat + (2 : Rat) ^ (-prec) :=
    Rat.lt_of_mul_lt_mul_right
      (calc x.toRat.inv * x.toRat
          = 1 := hinv_mul
        _ < (y.toRat + (2 : Rat) ^ (-prec)) * x.toRat := h2) (Rat.le_of_lt hxr)
  have hinv : invAtPrec x prec = x.toRat.inv.toDyadic prec := by
    unfold invAtPrec
    cases x with
    | zero => contradiction
    | ofOdd n k hn => rfl
  rw [hinv]
  exact eq_toDyadic_of_precision_le hp hyle hltinv

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
  have hbr : (0 : Rat) < b.toRat := by rwa [← toRat_lt_toRat_iff, toRat_zero] at hb
  rw [← toRat_le_toRat_iff, toRat_mul]
  unfold divAtPrec
  cases b with
  | zero => exfalso; contradiction
  | ofOdd n k hn =>
    simp only
    calc ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec).toRat * (ofOdd n k hn).toRat
        ≤ a.toRat / (ofOdd n k hn).toRat * (ofOdd n k hn).toRat :=
          Rat.mul_le_mul_of_nonneg_right Rat.toRat_toDyadic_le (Rat.le_of_lt hbr)
      _ = a.toRat := Rat.div_mul_cancel (Rat.ne_of_gt hbr)

/-- For a positive dyadic `b`, `a < (divAtPrec a b prec + 2^(-prec)) * b`. -/
theorem lt_divAtPrec_add_inc_mul {a b : Dyadic} (hb : 0 < b) (prec : Int) :
    a < (divAtPrec a b prec + ofIntWithPrec 1 prec) * b := by
  have hbr : (0 : Rat) < b.toRat := by rwa [← toRat_lt_toRat_iff, toRat_zero] at hb
  rw [← toRat_lt_toRat_iff, toRat_mul]
  unfold divAtPrec
  cases b with
  | zero => exfalso; contradiction
  | ofOdd n k hn =>
    simp only
    calc a.toRat
        = a.toRat / (ofOdd n k hn).toRat * (ofOdd n k hn).toRat :=
          (Rat.div_mul_cancel (Rat.ne_of_gt hbr)).symm
      _ < ((a.toRat / (ofOdd n k hn).toRat).toDyadic prec + ofIntWithPrec 1 prec).toRat
            * (ofOdd n k hn).toRat :=
          Rat.mul_lt_mul_of_pos_right Rat.lt_toRat_toDyadic_add hbr

/--
For positive `b`, `divAtPrec a b prec` is the unique dyadic with precision at most `prec`
satisfying both `_ * b ≤ a` and `a < (_ + ofIntWithPrec 1 prec) * b`.
-/
theorem eq_divAtPrec {a b : Dyadic} (hb : 0 < b) {prec : Int} {y : Dyadic}
    (hp : y.precision ≤ some prec) (h1 : y * b ≤ a)
    (h2 : a < (y + ofIntWithPrec 1 prec) * b) :
    y = divAtPrec a b prec := by
  have hbr : (0 : Rat) < b.toRat := by rwa [← toRat_lt_toRat_iff, toRat_zero] at hb
  have hbne : b.toRat ≠ 0 := Rat.ne_of_gt hbr
  rw [← toRat_le_toRat_iff, toRat_mul] at h1
  rw [← toRat_lt_toRat_iff, toRat_mul, toRat_add, toRat_ofIntWithPrec_eq_mul_two_pow,
      Rat.intCast_one, Rat.one_mul] at h2
  have hdiv_mul : a.toRat / b.toRat * b.toRat = a.toRat := Rat.div_mul_cancel hbne
  have hyle : y.toRat ≤ a.toRat / b.toRat :=
    Rat.le_of_mul_le_mul_right
      (calc y.toRat * b.toRat
          ≤ a.toRat := h1
        _ = a.toRat / b.toRat * b.toRat := hdiv_mul.symm) hbr
  have hltdiv : a.toRat / b.toRat < y.toRat + (2 : Rat) ^ (-prec) :=
    Rat.lt_of_mul_lt_mul_right
      (calc a.toRat / b.toRat * b.toRat
          = a.toRat := hdiv_mul
        _ < (y.toRat + (2 : Rat) ^ (-prec)) * b.toRat := h2) (Rat.le_of_lt hbr)
  have hdiv : divAtPrec a b prec = (a.toRat / b.toRat).toDyadic prec := by
    unfold divAtPrec
    cases b with
    | zero => contradiction
    | ofOdd n k hn => rfl
  rw [hdiv]
  exact eq_toDyadic_of_precision_le hp hyle hltdiv

end Dyadic
