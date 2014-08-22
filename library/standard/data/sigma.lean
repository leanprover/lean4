-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Leonardo de Moura, Jeremy Avigad

import logic.classes.inhabited logic.connectives.eq

using inhabited

inductive sigma {A : Type} (B : A → Type) : Type :=
| dpair : Πx : A, B x → sigma B

notation `Σ` binders `,` r:(scoped P, sigma P) := r

namespace sigma

section

  parameters {A : Type} {B : A → Type}

  abbreviation dpr1 (p : Σ x, B x) : A := sigma_rec (λ a b, a) p
  abbreviation dpr2 {A : Type} {B : A → Type} (p : Σ x, B x) : B (dpr1 p) := sigma_rec (λ a b, b) p

  theorem dpr1_dpair (a : A) (b : B a) : dpr1 (dpair a b) = a := refl a
  theorem dpr2_dpair (a : A) (b : B a) : dpr2 (dpair a b) = b := refl b

  -- TODO: remove prefix when we can protect it
  theorem sigma_destruct {P : sigma B → Prop} (p : sigma B) (H : ∀a b, P (dpair a b)) : P p :=
  sigma_rec H p

  theorem dpair_ext (p : sigma B) : dpair (dpr1 p) (dpr2 p) = p :=
  sigma_destruct p (take a b, refl _)

  -- Note that we give the general statment explicitly, to help the unifier
  theorem dpair_eq {a1 a2 : A} {b1 : B a1} {b2 : B a2} (H1 : a1 = a2) (H2 : eq_rec_on H1 b1 = b2) :
    dpair a1 b1 = dpair a2 b2 :=
  (show ∀(b2 : B a2) (H1 : a1 = a2) (H2 : eq_rec_on H1 b1 = b2), dpair a1 b1 = dpair a2 b2, from
    eq_rec
      (take (b2' : B a1),
	assume (H1' : a1 = a1),
	assume (H2' : eq_rec_on H1' b1 = b2'),
	show dpair a1 b1 = dpair a1 b2', from
	  calc
	    dpair a1 b1 = dpair a1 (eq_rec_on H1' b1) : {symm (eq_rec_on_id H1' b1)}
	      ... = dpair a1 b2' : {H2'}) H1)
  b2 H1 H2

  theorem sigma_eq {p1 p2 : Σx : A, B x} :
    ∀(H1 : dpr1 p1 = dpr1 p2) (H2 : eq_rec_on H1 (dpr2 p1) = (dpr2 p2)), p1 = p2 :=
  sigma_destruct p1 (take a1 b1, sigma_destruct p2 (take a2 b2 H1 H2, dpair_eq H1 H2))

  theorem sigma_inhabited [instance] (H1 : inhabited A) (H2 : inhabited (B (default A))) :
    inhabited (sigma B) :=
   inhabited_destruct H1 (λa, inhabited_destruct H2 (λb, inhabited_mk (dpair (default A) b)))

end

instance sigma_inhabited

end sigma
