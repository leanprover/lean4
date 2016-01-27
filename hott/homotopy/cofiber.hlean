/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Cofiber Type
-/
import hit.pointed_pushout function .susp

open eq pushout unit pointed is_trunc is_equiv susp unit

definition cofiber {A B : Type} (f : A → B) := pushout (λ (a : A), ⋆) f

namespace cofiber
  section
  parameters {A B : Type} (f : A → B)

  protected definition base [constructor] : cofiber f := inl ⋆

  protected definition cod [constructor] : B → cofiber f := inr

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

  protected definition rec {A : Type} {B : Type} {f : A → B} {P : cofiber f → Type}
    (Pinl : P (inl ⋆)) (Pinr : Π (x : B), P (inr x))
    (Pglue : Π (x : A), pathover P Pinl (glue x) (Pinr (f x))) :
    (Π y, P y) :=
  begin
    intro y, induction y, induction x, exact Pinl, exact Pinr x, esimp, exact Pglue x,
  end

  end
end cofiber

-- Pointed version

definition Cofiber {A B : Type*} (f : A →* B) : Type* := Pushout (pconst A Unit) f

namespace cofiber

  protected definition prec {A : Type*} {B : Type*}
    {f : A →* B} {P : Cofiber f → Type}
    (Pinl : P (inl ⋆)) (Pinr : Π (x : B), P (inr x))
    (Pglue : Π (x : A), pathover P Pinl (pglue x) (Pinr (f x))) :
    (Π (y : Cofiber f), P y) :=
  begin
    intro y, induction y, induction x, exact Pinl, exact Pinr x, esimp, exact Pglue x,
  end

  --TODO more pointed recursors

  variables (A : Type*)

  definition cofiber_unit : Cofiber (pconst A Unit) ≃* Susp A :=
  begin
    fconstructor,
    { fconstructor, intro x, induction x, exact north, exact south, exact merid x,
      reflexivity },
    { esimp, fapply adjointify,
      intro s, induction s, exact inl ⋆, exact inr ⋆, apply glue a,
      intro s, induction s, do 2 reflexivity, esimp,
      apply eq_pathover, refine _ ⬝hp !ap_id⁻¹, apply hdeg_square, 
      refine !(ap_compose (pushout.elim _ _ _)) ⬝ _, 
      refine ap _ !elim_merid ⬝ _, apply elim_glue,
      intro c, induction c with [n, s], induction n, reflexivity, 
      induction s, reflexivity, esimp, apply eq_pathover, apply hdeg_square, 
      refine _ ⬝ !ap_id⁻¹, refine !(ap_compose (pushout.elim _ _ _)) ⬝ _, 
      refine ap _ !elim_glue ⬝ _, apply elim_merid },
  end

end cofiber
