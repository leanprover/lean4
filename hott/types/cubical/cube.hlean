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
       (s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁)
       (s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁)
       (s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁)
       (s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁), Type :=
  idc : cube ids ids ids ids ids ids

  variables {A B : Type} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ a a' : A}
            {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂}
            {p₁₂₀ : a₀₂₀ = a₂₂₀} {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂}
            {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂} {p₀₂₁ : a₀₂₀ = a₀₂₂}
            {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
            {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
            {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
            {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
            {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
            {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
            {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
            {b₁ b₂ b₃ b₄ : B}

  definition idc    [reducible] [constructor]         := @cube.idc
  definition idcube [reducible] [constructor] (a : A) := @cube.idc A a
  definition rfl1 : cube s₁₁₀ s₁₁₀ vrfl vrfl vrfl vrfl := by induction s₁₁₀; exact idc
  definition rfl2 : cube vrfl vrfl s₁₁₀ s₁₁₀ hrfl hrfl := by induction s₁₁₀; exact idc
  definition rfl3 : cube hrfl hrfl hrfl hrfl s₁₀₁ s₁₀₁ := by induction s₁₀₁; exact idc

  definition eq_of_cube (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁) :
    transpose s₁₀₁⁻¹ᵛ ⬝h s₁₁₀ ⬝h transpose s₁₂₁ =
      whisker_square (eq_bot_of_square s₀₁₁) (eq_bot_of_square s₂₁₁) idp idp s₁₁₂ :=
  by induction c; reflexivity

  --set_option pp.implicit true
  definition eq_of_vdeg_cube {s s' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
    (c : cube s s' vrfl vrfl vrfl vrfl) : s = s' :=
  begin
    induction s, exact eq_of_cube c
  end

  definition square_pathover [unfold 7]
    {f₁ : A → b₁ = b₂} {f₂ : A → b₃ = b₄} {f₃ : A → b₁ = b₃} {f₄ : A → b₂ = b₄}
    {p : a = a'}
    {q : square (f₁ a) (f₂ a) (f₃ a) (f₄ a)} {r : square (f₁ a') (f₂ a') (f₃ a') (f₄ a')}
    (s : cube q r (vdeg_square (ap f₁ p)) (vdeg_square (ap f₂ p))
                  (vdeg_square (ap f₃ p)) (vdeg_square (ap f₄ p))) : q =[p] r :=
  by induction p;apply pathover_idp_of_eq;exact eq_of_vdeg_cube s


end eq
