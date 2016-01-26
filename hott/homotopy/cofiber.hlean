/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Cofiber Type
-/
import hit.pointed_pushout function

open eq pushout unit pointed is_trunc is_equiv

definition cofiber {A B : Type} (f : A → B) := pushout (λ (a : A), ⋆) f

namespace cofiber
  section
  parameters {A B : Type} (f : A → B)

  protected definition base : cofiber f := inl ⋆

  protected definition cod : B → cofiber f := inr

  protected definition contr_of_equiv [H : is_equiv f] : is_contr (cofiber f) :=
  begin
    fapply is_contr.mk, exact base,
    intro a, induction a with [u, b],
    { cases u, reflexivity },
    { exact !glue ⬝ ap inr (right_inv f b) },
    { apply eq_pathover, refine _ ⬝hp !ap_id⁻¹, refine !ap_constant ⬝ph _, 
      apply move_bot_of_left, refine !idp_con ⬝ph _, apply transpose, esimp,
      refine _ ⬝hp (ap (ap inr) !adj⁻¹), refine _ ⬝hp !ap_compose, apply square_Flr_idp_ap },
  end

  end
end cofiber

-- Pointed version

definition Cofiber {A B : Type*} (f : A →* B) : Type* := Pushout (pconst A Unit) f


