/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
import Init.Data.Dyadic.Basic

/-!
# Inversion for dyadic numbers
-/

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
  sorry

/-- For a positive dyadic `x`, `1 < (invAtPrec x prec + 2^(-prec)) * x` when the increment doesn't overflow. -/
theorem one_lt_invAtPrec_add_inc_mul {x : Dyadic} (hx : 0 < x) (prec : Int) :
    1 < (invAtPrec x prec + ofIntWithPrec 1 prec) * x := by
  sorry

end Dyadic