/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Cubes
-/

import .square

open equiv equiv.ops is_equiv sigma sigma.ops

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
            (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁)

  definition idc    [reducible] [constructor]         := @cube.idc
  definition idcube [reducible] [constructor] (a : A) := @cube.idc A a

  variables (s₁₁₀ s₁₀₁)
  definition refl1 : cube s₁₁₀ s₁₁₀ vrfl vrfl vrfl vrfl :=
  by induction s₁₁₀; exact idc

  definition refl2 : cube vrfl vrfl s₁₁₀ s₁₁₀ hrfl hrfl :=
  by induction s₁₁₀; exact idc
  
  definition refl3 : cube hrfl hrfl hrfl hrfl s₁₀₁ s₁₀₁ :=
  by induction s₁₀₁; exact idc

  variables {s₁₁₀ s₁₀₁}
  definition rfl1 : cube s₁₁₀ s₁₁₀ vrfl vrfl vrfl vrfl := !refl1

  definition rfl2 : cube vrfl vrfl s₁₁₀ s₁₁₀ hrfl hrfl := !refl2

  definition rfl3 : cube hrfl hrfl hrfl hrfl s₁₀₁ s₁₀₁ := !refl3

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
    {q : square (f₁ a) (f₂ a) (f₃ a) (f₄ a)}
    {r : square (f₁ a') (f₂ a') (f₃ a') (f₄ a')}
    (s : cube q r (vdeg_square (ap f₁ p)) (vdeg_square (ap f₂ p))
                  (vdeg_square (ap f₃ p)) (vdeg_square (ap f₄ p))) : q =[p] r :=
  by induction p;apply pathover_idp_of_eq;exact eq_of_vdeg_cube s

  /- Transporting along a square -/

  definition cube_transport110 {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀}
    (p : s₁₁₀ = s₁₁₀') (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁) :
    cube s₁₁₀' s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ :=
  by induction p; exact c

  definition cube_transport112 {s₁₁₂' : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
    (p : s₁₁₂ = s₁₁₂') (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁) :
    cube s₁₁₀ s₁₁₂' s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ :=
  by induction p; exact c

  definition cube_transport011 {s₀₁₁' : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁}
    (p : s₀₁₁ = s₀₁₁') (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁) :
    cube s₁₁₀ s₁₁₂ s₀₁₁' s₂₁₁ s₁₀₁ s₁₂₁ :=
  by induction p; exact c

  definition cube_transport211 {s₂₁₁' : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
    (p : s₂₁₁ = s₂₁₁') (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁) :
    cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁' s₁₀₁ s₁₂₁ :=
  by induction p; exact c

  definition cube_transport101 {s₁₀₁' : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁}
    (p : s₁₀₁ = s₁₀₁') (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁) :
    cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁' s₁₂₁ :=
  by induction p; exact c

  definition cube_transport121 {s₁₂₁' : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
    (p : s₁₂₁ = s₁₂₁') (c : cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁) :
    cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁' :=
  by induction p; exact c

  /- Each equality between squares leads to a cube which is degenerate in one
     dimension. -/

  definition deg1_cube {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (p : s₁₁₀ = s₁₁₀') :
    cube s₁₁₀ s₁₁₀' vrfl vrfl vrfl vrfl :=
  by induction p; exact rfl1

  definition deg2_cube {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (p : s₁₁₀ = s₁₁₀') :
    cube vrfl vrfl s₁₁₀ s₁₁₀' hrfl hrfl :=
  by induction p; exact rfl2

  definition deg3_cube {s₁₁₀' : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} (p : s₁₁₀ = s₁₁₀') :
    cube hrfl hrfl hrfl hrfl s₁₁₀ s₁₁₀' :=
  by induction p; exact rfl3

  /- For each square of parralel equations, there are cubes where the square's
     sides appear in a degenerated way and two opposite sides are ids's -/

  section
  variables {a₀ a₁ : A} {p₀₀ p₀₂ p₂₀ p₂₂ : a₀ = a₁} {s₁₀ : p₀₀ = p₂₀}
    {s₁₂ : p₀₂ = p₂₂} {s₀₁ : p₀₀ = p₀₂} {s₂₁ : p₂₀ = p₂₂}
    (sq : square s₁₀ s₁₂ s₀₁ s₂₁)
  
  include sq
  
  definition ids1_cube_of_square : cube ids ids (hdeg_square s₀₁)
    (hdeg_square s₂₁) (hdeg_square s₁₀) (hdeg_square s₁₂) :=
  by induction p₀₀; induction sq; apply idc

  definition ids2_cube_of_square : cube (hdeg_square s₀₁) (hdeg_square s₂₁) ids ids
    (vdeg_square s₁₀) (vdeg_square s₁₂) :=
  by induction p₀₀; induction sq; apply idc

  definition ids3_cube_of_square : cube (vdeg_square s₀₁) (vdeg_square s₂₁)
    (vdeg_square s₁₀) (vdeg_square s₁₂) ids ids :=
  by induction p₀₀; induction sq; apply idc

  end

  /- Cube fillers -/

  section cube_fillers
  variables (s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁)

  definition cube_fil110 : Σ lid, cube lid s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ :=
  begin
    induction s₀₁₁, induction s₂₁₁,
    let fillsq := square_fill_l (eq_of_vdeg_square s₁₀₁) 
        (eq_of_hdeg_square s₁₁₂) (eq_of_vdeg_square s₁₂₁),
    apply sigma.mk,
    apply cube_transport101 (left_inv (vdeg_square_equiv _ _) s₁₀₁),
    apply cube_transport112 (left_inv (hdeg_square_equiv _ _) s₁₁₂),
    apply cube_transport121 (left_inv (vdeg_square_equiv _ _) s₁₂₁),
    apply ids2_cube_of_square, exact fillsq.2
  end

  definition cube_fill112 : Σ lid, cube s₁₁₀ lid s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ :=
  begin
    induction s₀₁₁, induction s₂₁₁,
    let fillsq := square_fill_r (eq_of_vdeg_square s₁₀₁) 
        (eq_of_hdeg_square s₁₁₀) (eq_of_vdeg_square s₁₂₁),
    apply sigma.mk,
    apply cube_transport101 (left_inv (vdeg_square_equiv _ _) s₁₀₁),
    apply cube_transport110 (left_inv (hdeg_square_equiv _ _) s₁₁₀),
    apply cube_transport121 (left_inv (vdeg_square_equiv _ _) s₁₂₁),
    apply ids2_cube_of_square, exact fillsq.2,
  end

  definition cube_fill011 : Σ lid, cube s₁₁₀ s₁₁₂ lid s₂₁₁ s₁₀₁ s₁₂₁ :=
  begin
    induction s₁₀₁, induction s₁₂₁,
    let fillsq := square_fill_t (eq_of_vdeg_square s₁₁₀) (eq_of_vdeg_square s₁₁₂)
      (eq_of_vdeg_square s₂₁₁),
    apply sigma.mk,
    apply cube_transport110 (left_inv (vdeg_square_equiv _ _) s₁₁₀),
    apply cube_transport211 (left_inv (vdeg_square_equiv _ _) s₂₁₁),
    apply cube_transport112 (left_inv (vdeg_square_equiv _ _) s₁₁₂),
    apply ids3_cube_of_square, exact fillsq.2,
  end

  definition cube_fill211 : Σ lid, cube s₁₁₀ s₁₁₂ s₀₁₁ lid s₁₀₁ s₁₂₁ :=
  begin
    induction s₁₀₁, induction s₁₂₁,
    let fillsq := square_fill_b (eq_of_vdeg_square s₀₁₁) (eq_of_vdeg_square s₁₁₀)
      (eq_of_vdeg_square s₁₁₂),
    apply sigma.mk,
    apply cube_transport011 (left_inv (vdeg_square_equiv _ _) s₀₁₁),
    apply cube_transport110 (left_inv (vdeg_square_equiv _ _) s₁₁₀),
    apply cube_transport112 (left_inv (vdeg_square_equiv _ _) s₁₁₂),
    apply ids3_cube_of_square, exact fillsq.2,
  end

  definition cube_fill101 : Σ lid, cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ lid s₁₂₁ :=
  begin
    induction s₁₁₀, induction s₁₁₂,
    let fillsq := square_fill_t (eq_of_hdeg_square s₀₁₁) (eq_of_hdeg_square s₂₁₁)
      (eq_of_hdeg_square s₁₂₁),
    apply sigma.mk,
    apply cube_transport011 (left_inv (hdeg_square_equiv _ _) s₀₁₁),
    apply cube_transport211 (left_inv (hdeg_square_equiv _ _) s₂₁₁),
    apply cube_transport121 (left_inv (hdeg_square_equiv _ _) s₁₂₁),
    apply ids1_cube_of_square, exact fillsq.2,
  end

  definition cube_fill121 : Σ lid, cube s₁₁₀ s₁₁₂ s₀₁₁ s₂₁₁ s₁₀₁ lid :=
  begin
    induction s₁₁₀, induction s₁₁₂,
    let fillsq := square_fill_b (eq_of_hdeg_square s₁₀₁) (eq_of_hdeg_square s₀₁₁)
      (eq_of_hdeg_square s₂₁₁),
    apply sigma.mk,
    apply cube_transport101 (left_inv (hdeg_square_equiv _ _) s₁₀₁),
    apply cube_transport011 (left_inv (hdeg_square_equiv _ _) s₀₁₁),
    apply cube_transport211 (left_inv (hdeg_square_equiv _ _) s₂₁₁),
    apply ids1_cube_of_square, exact fillsq.2,
  end

  end cube_fillers

end eq
