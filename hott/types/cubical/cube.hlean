/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Cubes
-/

import .square

open equiv is_equiv

namespace eq

  inductive cube {A : Type} {a₀₀₀ : A}
    : Π{a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
       {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
       {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
       {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
       {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
       (s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀)
       (s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂)
       (s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁)
       (s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁)
       (s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁)
       (s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁), Type :=
  idc : cube ids ids ids ids ids ids

  variables {A : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
            {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
            {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
            {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
            {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
            {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
            {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
            {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
            {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
            {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
            {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}

  definition idc    [reducible] [constructor]         := @cube.idc
  definition idcube [reducible] [constructor] (a : A) := @cube.idc A a
  definition rfl1 : cube s₁₁₀ s₁₁₀ vrfl vrfl vrfl vrfl := by induction s₁₁₀; exact idc
  definition rfl2 : cube hrfl hrfl s₁₀₁ s₁₀₁ hrfl hrfl := by induction s₁₀₁; exact idc
  definition rfl3 : cube vrfl vrfl hrfl hrfl s₁₁₀ s₁₁₀ := by induction s₁₁₀; exact idc


end eq
