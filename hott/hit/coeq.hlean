/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: hit.coeq
Authors: Floris van Doorn

Declaration of the coequalizer
-/

import .colimit

open colimit bool eq

namespace coeq
context

universe u
parameters {A B : Type.{u}} (f g : A → B)

  definition coeq_diag [reducible] : diagram :=
  diagram.mk bool
             bool
             (λi, bool.rec_on i A B)
             (λj, ff)
             (λj, tt)
             (λj, bool.rec_on j f g)

  local notation `D` := coeq_diag

  definition coeq := colimit coeq_diag -- TODO: define this in root namespace
  local attribute coeq_diag [instance]

  definition coeq_i (x : B) : coeq :=
  @ι _ _ x

  /- cp is the name Coq uses. I don't know what it abbreviates, but at least it's short :-) -/
  definition cp (x : A) : coeq_i (f x) = coeq_i (g x) :=
  @cglue _ _ x ⬝ (@cglue _ _ x)⁻¹

  protected definition rec {P : coeq → Type} (P_i : Π(x : B), P (coeq_i x))
    (Pcp : Π(x : A), cp x ▹ P_i (f x) = P_i (g x)) (y : coeq) : P y :=
  begin
    fapply (@colimit.rec_on _ _ y),
    { intros [i, x], cases i,
        exact (@cglue _ _ x ▹ P_i (f x)),
        apply P_i},
    { intros [j, x], cases j,
        exact idp,
      esimp [coeq_diag],
      apply tr_eq_of_eq_inv_tr,
      apply concat, rotate 1, apply tr_con,
      rewrite -Pcp}
  end

  protected definition rec_on [reducible] {P : coeq → Type} (y : coeq)
    (P_i : Π(x : B), P (coeq_i x)) (Pcp : Π(x : A), cp x ▹ P_i (f x) = P_i (g x)) : P y :=
  rec P_i Pcp y

  protected definition elim {P : Type} (P_i : B → P)
    (Pcp : Π(x : A), P_i (f x) = P_i (g x)) (y : coeq) : P :=
  rec P_i (λx, !tr_constant ⬝ Pcp x) y

  protected definition elim_on [reducible] {P : Type} (y : coeq) (P_i : B → P)
    (Pcp : Π(x : A), P_i (f x) = P_i (g x)) : P :=
  elim P_i Pcp y

  definition rec_cp {P : coeq → Type} (P_i : Π(x : B), P (coeq_i x))
    (Pcp : Π(x : A), cp x ▹ P_i (f x) = P_i (g x))
      (x : A) : apD (rec P_i Pcp) (cp x) = sorry ⬝ Pcp x ⬝ sorry :=
  sorry

  definition elim_cp {P : Type} (P_i : B → P) (Pcp : Π(x : A), P_i (f x) = P_i (g x))
    (x : A) : ap (elim P_i Pcp) (cp x) = sorry ⬝ Pcp x ⬝ sorry :=
  sorry

end

end coeq
