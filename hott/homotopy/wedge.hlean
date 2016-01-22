/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Wedge Sum of Two Pointed Types
-/
import hit.pointed_pushout

open eq pushout pointed Pointed

namespace wedge
  section
  variables (A B : Type*)

  definition Wedge : Type* := Pushout (pconst Unit A) (pconst Unit B)

  -- TODO maybe find a cleaner proof
  protected definition unit : A ≃* Wedge Unit A :=
  begin
    fconstructor,
    { fapply pmap.mk, intro a, apply pinr a, apply respect_pt },
    { fapply is_equiv.adjointify, intro x, fapply pushout.elim_on x, 
      exact λ x, Point A, exact id, intro u, reflexivity, 
      intro x, fapply pushout.rec_on x, intro u, cases u, esimp, apply (glue unit.star)⁻¹, 
      intro a, reflexivity,
      intro u, cases u, esimp, apply eq_pathover,
      refine _ ⬝hp !ap_id⁻¹, fapply eq_hconcat, apply ap_compose inr, 
      krewrite elim_glue, fapply eq_hconcat, apply ap_idp, apply square_of_eq, 
      apply con.left_inv, 
      intro a, reflexivity },
  end

  end
end wedge
