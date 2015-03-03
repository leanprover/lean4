/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.fiber
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about fibers
-/

import types.sigma types.eq

structure fiber {A B : Type} (f : A → B) (b : B) :=
  (point : A)
  (point_eq : f point = b)

open equiv sigma sigma.ops eq

namespace fiber
  variables {A B : Type} (f : A → B) (b : B)

  definition sigma_char : fiber f b ≃ (Σ(a : A), f a = b) :=
  begin
  fapply equiv.MK,
    {intro x, exact ⟨point x, point_eq x⟩},
    {intro x, exact (fiber.mk x.1 x.2)},
    {intro x, cases x, apply idp},
    {intro x, cases x, apply idp},
  end
  --set_option pp.notation false


  definition equiv_fiber_eq (x y : fiber f b)
    : (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
  begin
    apply equiv.trans,
      {apply eq_equiv_fn_eq_of_equiv, apply sigma_char},
    apply equiv.trans,
      {apply equiv.symm, apply equiv_sigma_eq},
    apply sigma_equiv_sigma_id,
    intro p,
    apply equiv_of_equiv_of_eq,
      {apply (ap (λx, x = _)), apply transport_paths_Fl}

    -- apply equiv_of_eq,
    -- fapply (apD011 @sigma),
    --   {apply idp},
    -- esimp
  end

  definition fiber_eq : (p : u.1 = v.1) (q : p ▹ u.2 = v.2) : u = v :=
  by cases u; cases v; apply (dpair_eq_dpair p q)

end fiber



namespace is_equiv
  open equiv
  context
    parameters {A B : Type} (f : A → B) [H : is_equiv f]
    include H


  end
  variables {A B : Type} (f : A → B)

  theorem is_hprop_is_equiv [instance] : is_hprop (is_equiv f) :=
  sorry

end is_equiv

namespace equiv
  open is_equiv
  variables {A B : Type}

  protected definition eq_mk' {f f' : A → B} [H : is_equiv f] [H' : is_equiv f'] (p : f = f')
      : equiv.mk f H = equiv.mk f' H' :=
  apD011 equiv.mk p !is_hprop.elim

  protected definition eq_mk {f f' : A ≃ B} (p : to_fun f = to_fun f') : f = f' :=
  by (cases f; cases f'; apply (equiv.eq_mk' p))
end equiv
