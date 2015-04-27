/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: types.fiber
Author: Floris van Doorn

Ported from Coq HoTT
Theorems about fibers
-/

import .sigma .eq

structure fiber {A B : Type} (f : A → B) (b : B) :=
  (point : A)
  (point_eq : f point = b)

open equiv sigma sigma.ops eq

namespace fiber
  variables {A B : Type} {f : A → B} {b : B}

  definition sigma_char (f : A → B) (b : B) : fiber f b ≃ (Σ(a : A), f a = b) :=
  begin
  fapply equiv.MK,
    {intro x, exact ⟨point x, point_eq x⟩},
    {intro x, exact (fiber.mk x.1 x.2)},
    {intro x, cases x, apply idp},
    {intro x, cases x, apply idp},
  end

  definition fiber_eq_equiv (x y : fiber f b)
    : (x = y) ≃ (Σ(p : point x = point y), point_eq x = ap f p ⬝ point_eq y) :=
  begin
    apply equiv.trans,
      {apply eq_equiv_fn_eq_of_equiv, apply sigma_char},
    apply equiv.trans,
      {apply equiv.symm, apply equiv_sigma_eq},
    apply sigma_equiv_sigma_id,
    intro p,
    apply equiv_of_equiv_of_eq,
    rotate 1,
    apply inv_con_eq_equiv_eq_con,
    {apply (ap (λx, x = _)), rewrite transport_eq_Fl}
  end

  definition fiber_eq {x y : fiber f b} (p : point x = point y)
    (q : point_eq x = ap f p ⬝ point_eq y) : x = y :=
  to_inv !fiber_eq_equiv ⟨p, q⟩

end fiber
