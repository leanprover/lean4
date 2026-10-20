/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Round

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model.UnpackedFloat

/--
Computes the product of two floating-point numbers and rounds the result according to
the given specification.
-/
def mul (spec : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _ => .notANumber
  | _, .notANumber => .notANumber
  | .infinity sign₁, .infinity sign₂ => .infinity (sign₁ * sign₂)
  | .infinity sign₁, .finite sign₂ .. => .infinity (sign₁ * sign₂)
  | .finite sign₁ .., .infinity sign₂ => .infinity (sign₁ * sign₂)
  | .infinity _, .zero _ => .notANumber
  | .zero _, .infinity _ => .notANumber
  | .finite sign₁ .., .zero sign₂ => .zero (sign₁ * sign₂)
  | .zero sign₁, .finite sign₂ .. => .zero (sign₁ * sign₂)
  | .zero sign₁, .zero sign₂ => .zero (sign₁ * sign₂)
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _ =>
    roundWithAccuracy spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact

end Float.Model.UnpackedFloat
