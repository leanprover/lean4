/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Smash Product of Types
-/

import hit.pushout .wedge .cofiber .susp .sphere

open eq pushout prod pointed Pointed

definition product_of_wedge [constructor] (A B : Type*) : Wedge A B →* A ×* B :=
begin
  fconstructor,
  intro x, induction x with [a, b], exact (a, point B), exact (point A, b), 
  do 2 reflexivity
end

definition Smash (A B : Type*) := Cofiber (product_of_wedge A B)

open sphere susp unit

namespace smash

  definition smash_bool (X : Type*) : Smash X Bool ≃* X :=
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
      { intro s, esimp, induction s, } }
  end

  check ap_compose


  check bool.rec

exit
fconstructor, intro x, induction x, exact point X,
      induction a, exact point X, esimp, induction x, do 2 reflexivity, 
      apply eq_pathover, apply hdeg_square, induction x, -/


  definition susp_equiv_circle_smash (X : Type*) : Susp X ≃* Smash (Sphere 1) X :=
  begin
    fconstructor,
    { fconstructor, intro x, induction x, },
  end

end smash
