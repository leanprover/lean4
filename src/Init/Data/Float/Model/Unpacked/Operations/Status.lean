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
Returns `true` if the float represents a real number, i.e., it is neither infinite nor `NaN`.
-/
def isFinite : UnpackedFloat → Bool
  | .notANumber => false
  | .infinity .. => false
  | .zero .. => true
  | .finite .. => true

/--
Returns `true` if the float is positive or negative infinity.
-/
def isInf : UnpackedFloat → Bool
  | .infinity .. => true
  | _ => false

/--
Returns `true` if the float is `NaN`.
-/
def isNaN : UnpackedFloat → Bool
  | .notANumber => true
  | _ => false

end Float.Model.UnpackedFloat
