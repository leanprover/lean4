/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Basic

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model.UnpackedFloat

/--
Computes the ordering between the two floats as specificed by IEEE. Returns an
`Option Ordering` to account for the fact that `NaN` is incomparable with everything.
Also, positive and negative zero are equal.

Important: this operation only works correctly if the two inputs are in
canonical form for a common format (see the docstring for `UnpackedFloat` for details.)
-/
protected def compare : UnpackedFloat → UnpackedFloat → Option Ordering
  | .notANumber, _ => none
  | _, .notANumber => none
  | .infinity s₁, .infinity s₂ => some (compare s₁ s₂)
  | .infinity .positive, _ => some .gt
  | .infinity .negative, _ => some .lt
  | _, .infinity .positive => some .lt
  | _, .infinity .negative => some .gt
  | .finite .positive .., .zero _ => some .gt
  | .finite .negative .., .zero _ => some .lt
  | .zero _, .finite .positive .. => some .lt
  | .zero _, .finite .negative .. => some .gt
  | .zero _, .zero _ => some .eq
  | .finite .negative m₁ e₁ _, .finite .negative m₂ e₂ _ =>
    some ((compare e₁ e₂).then (compare m₁ m₂)).swap
  | .finite .negative .., .finite .positive .. => some .lt
  | .finite .positive .., .finite .negative .. => some .gt
  | .finite .positive m₁ e₁ _, .finite .positive m₂ e₂ _ =>
    some ((compare e₁ e₂).then (compare m₁ m₂))

/--
Determines whether `a` is less than or equal to `b` according to IEEE rules.

This is not a total ordering, and `≤` is not reflexive.
-/
protected def le (a b : UnpackedFloat) : Bool :=
  (a.compare b).any (·.isLE)

/--
Determines whether `a` is less than `b` according to IEEE rules.

This is not a total ordering.
-/
protected def lt (a b : UnpackedFloat) : Bool :=
  a.compare b == some .lt

/--
Determines whether `a` is equal to `b` according to IEEE rules.

This is not a reflexive relation.
-/
protected def beq (a b : UnpackedFloat) : Bool :=
  a.compare b == some .eq

end Float.Model.UnpackedFloat
