/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Round

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model.UnpackedFloat

/--
Computes the fused multiply-add `x * y + z` of three floating point numbers and rounds the
result according to the given specification. The product `x * y` is exact and never rounded
on its own; only the final sum is rounded.
-/
def fma (spec : Format) : UnpackedFloat → UnpackedFloat → UnpackedFloat → UnpackedFloat
  | .notANumber, _, _ => .notANumber
  | _, .notANumber, _ => .notANumber
  | _, _, .notANumber => .notANumber
  | .zero _, .infinity _, _ => .notANumber
  | .infinity _, .zero _, _ => .notANumber
  | .infinity sign₁, .infinity sign₂, .infinity sign₃ =>
    if sign₁ * sign₂ == sign₃ then .infinity sign₃ else .notANumber
  | .infinity sign₁, .finite sign₂ .., .infinity sign₃ =>
    if sign₁ * sign₂ == sign₃ then .infinity sign₃ else .notANumber
  | .finite sign₁ .., .infinity sign₂, .infinity sign₃ =>
    if sign₁ * sign₂ == sign₃ then .infinity sign₃ else .notANumber
  | .infinity sign₁, .infinity sign₂, _ => .infinity (sign₁ * sign₂)
  | .infinity sign₁, .finite sign₂ .., _ => .infinity (sign₁ * sign₂)
  | .finite sign₁ .., .infinity sign₂, _ => .infinity (sign₁ * sign₂)
  | _, _, .infinity sign₃ => .infinity sign₃
  | .zero sign₁, .zero sign₂, .zero sign₃ =>
    if sign₁ * sign₂ == sign₃ then .zero sign₃ else .zero .positive
  | .zero sign₁, .finite sign₂ .., .zero sign₃ =>
    if sign₁ * sign₂ == sign₃ then .zero sign₃ else .zero .positive
  | .finite sign₁ .., .zero sign₂, .zero sign₃ =>
    if sign₁ * sign₂ == sign₃ then .zero sign₃ else .zero .positive
  | .zero _, _, z => z
  | _, .zero _, z => z
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _, .zero _ =>
    roundWithAccuracy spec (s₁ * s₂) (m₁ * m₂) (e₁ + e₂) .exact
  | .finite s₁ m₁ e₁ _, .finite s₂ m₂ e₂ _, .finite s₃ m₃ e₃ _ =>
    let productMantissa := m₁ * m₂
    let productExponent := e₁ + e₂
    let smallerExponent := min productExponent e₃
    let (productMantissa, _) := decreaseExponent productMantissa productExponent smallerExponent
    let (m₃, _) := decreaseExponent m₃ e₃ smallerExponent
    let mantissa := (s₁ * s₂).apply productMantissa + s₃.apply m₃
    normalize spec mantissa smallerExponent .positive

end Float.Model.UnpackedFloat
