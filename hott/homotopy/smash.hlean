/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Smash Product of Types
-/

import hit.pushout .wedge .cofiber .susp .sphere

open eq pushout prod pointed Pointed is_trunc

definition product_of_wedge [constructor] (A B : Type*) : Wedge A B →* A ×* B :=
begin
  fconstructor,
  intro x, induction x with [a, b], exact (a, point B), exact (point A, b), 
  do 2 reflexivity
end

definition Smash (A B : Type*) := Cofiber (product_of_wedge A B)

open sphere susp unit

namespace smash

  protected definition prec {X Y : Type*} {P : Smash X Y → Type}
    (pxy : Π x y, P (inr (x, y))) (ps : P (inl ⋆))
    (px : Π x, pathover P ps (glue (inl x)) (pxy x (point Y)))
    (py : Π y, pathover P ps (glue (inr y)) (pxy (point X) y))
    (pg : pathover (λ x, pathover P ps (glue x) (@prod.rec X Y (λ x, P (inr x)) pxy
          (pushout.elim (λ a, (a, Point Y)) (pair (Point X)) (λ x, idp) x)))
          (px (Point X)) (glue ⋆) (py (Point Y))) : Π s, P s :=
  begin
    intro s, induction s, induction x, exact ps,
    induction x with [x, y], exact pxy x y,
    induction x with [x, y, u], exact px x, exact py y,
    induction u, exact pg,
  end

  protected definition prec_on {X Y : Type*} {P : Smash X Y → Type} (s : Smash X Y)
    (pxy : Π x y, P (inr (x, y))) (ps : P (inl ⋆))
    (px : Π x, pathover P ps (glue (inl x)) (pxy x (point Y)))
    (py : Π y, pathover P ps (glue (inr y)) (pxy (point X) y))
    (pg : pathover (λ x, pathover P ps (glue x) (@prod.rec X Y (λ x, P (inr x)) pxy
          (pushout.elim (λ a, (a, Point Y)) (pair (Point X)) (λ x, idp) x)))
          (px (Point X)) (glue ⋆) (py (Point Y))) : P s :=
  smash.prec pxy ps px py pg s

/-  definition smash_bool (X : Type*) : Smash X Bool ≃* X :=
  begin
    fconstructor,
    { fconstructor,
      { intro x, fapply cofiber.pelim_on x, clear x, exact point X, intro p,
        cases p with [x', b], cases b with [x, x'], exact point X, exact x',
        clear x, intro w, induction w with [y, b], reflexivity, 
        cases b, reflexivity, reflexivity, esimp,
        apply eq_pathover, refine !ap_constant ⬝ph _, cases x, esimp, apply hdeg_square,
        apply inverse, apply concat, apply ap_compose (λ a, prod.cases_on a _),
        apply concat, apply ap _ !elim_glue, reflexivity },
      reflexivity },
    { fapply is_equiv.adjointify,
      { intro x, apply inr, exact pair x bool.tt },
      { intro x, reflexivity },
      { intro s, esimp, induction s,
        { cases x, apply (glue (inr bool.tt))⁻¹ },
        { cases x with [x, b], cases b, 
          apply inverse, apply concat, apply (glue (inl x))⁻¹, apply (glue (inr bool.tt)),
          reflexivity }, 
        { esimp, apply eq_pathover, induction x, 
          esimp, apply hinverse, krewrite ap_id, apply move_bot_of_left, 
          krewrite con.right_inv,
          refine _ ⬝hp !(ap_compose (λ a, inr (pair a _)))⁻¹,
          apply transpose, apply square_of_eq_bot, rewrite [con_idp, con.left_inv],
          apply inverse, apply concat, apply ap (ap _), 
           } } }

  definition susp_equiv_circle_smash (X : Type*) : Susp X ≃* Smash (Sphere 1) X :=
  begin
    fconstructor,
    { fconstructor, intro x, induction x, },
  end-/

end smash
