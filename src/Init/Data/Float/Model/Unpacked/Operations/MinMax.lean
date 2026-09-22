/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Operations.Compare

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model.UnpackedFloat

/--
Computes the IEEE-754-2019 `minimum` of two floats. The result is `NaN` if either operand is
`NaN`; otherwise it is the smaller operand, where `-0` is considered smaller than `+0`.

Important: this operation only works correctly if the two inputs are in
canonical form for a common format (see the docstring for `UnpackedFloat` for details.)
-/
def minimum : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .zero .negative, .zero _ => .zero .negative
  | .zero .positive, .zero s => .zero s
  | a, b => if a.le b then a else b

/--
Computes the IEEE-754-2019 `minimumNumber` of two floats. A `NaN` operand is ignored in favor of
the other operand, so the result is `NaN` only if both operands are `NaN`; otherwise it is the
smaller operand, where `-0` is considered smaller than `+0`.

Important: this operation only works correctly if the two inputs are in
canonical form for a common format (see the docstring for `UnpackedFloat` for details.)
-/
def minimumNumber : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, b => b
  | a, .notANumber => a
  | .zero .negative, .zero _ => .zero .negative
  | .zero .positive, .zero s => .zero s
  | a, b => if a.le b then a else b

/--
Computes the IEEE-754-2019 `maximum` of two floats. The result is `NaN` if either operand is
`NaN`; otherwise it is the larger operand, where `-0` is considered smaller than `+0`.

Important: this operation only works correctly if the two inputs are in
canonical form for a common format (see the docstring for `UnpackedFloat` for details.)
-/
def maximum : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .zero .positive, .zero _ => .zero .positive
  | .zero .negative, .zero s => .zero s
  | a, b => if a.le b then b else a

/--
Computes the IEEE-754-2019 `maximumNumber` of two floats. A `NaN` operand is ignored in favor of
the other operand, so the result is `NaN` only if both operands are `NaN`; otherwise it is the
larger operand, where `-0` is considered smaller than `+0`.

Important: this operation only works correctly if the two inputs are in
canonical form for a common format (see the docstring for `UnpackedFloat` for details.)
-/
def maximumNumber : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, b => b
  | a, .notANumber => a
  | .zero .positive, .zero _ => .zero .positive
  | .zero .negative, .zero s => .zero s
  | a, b => if a.le b then b else a

end Float.Model.UnpackedFloat
