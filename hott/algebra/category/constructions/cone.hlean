/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Cones
-/

import ..nat_trans

open functor nat_trans eq equiv is_trunc

namespace category

  structure cone_obj {I C : Precategory} (F : I ⇒ C) :=
  (c : C)
  (η : constant_functor I c ⟹ F)

  local attribute cone_obj.c [coercion]

  variables {I C : Precategory} {F : I ⇒ C} {x y z : cone_obj F}
  structure cone_hom (x y : cone_obj F) :=
  (f : x ⟶ y)
  (p : Πi, cone_obj.η y i ∘ f = cone_obj.η x i)

  local attribute cone_hom.f [coercion]

  definition cone_id [constructor] (x : cone_obj F) : cone_hom x x :=
  cone_hom.mk id
              (λi, !id_right)

  definition cone_comp [constructor] (g : cone_hom y z) (f : cone_hom x y) : cone_hom x z :=
  cone_hom.mk (cone_hom.f g ∘ cone_hom.f f)
              abstract λi, by rewrite [assoc, +cone_hom.p] end

  definition is_hprop_hom_eq [instance] [priority 1001] {ob : Type} [C : precategory ob] {x y : ob} (f g : x ⟶ y)
    : is_hprop (f = g) :=
  _

  theorem cone_hom_eq {f f' : cone_hom x y} (q : cone_hom.f f = cone_hom.f f') : f = f' :=
  begin
    induction f, induction f', esimp at *, induction q, apply ap (cone_hom.mk f),
    apply @is_hprop.elim, apply pi.is_trunc_pi, intro x, apply is_trunc_eq, -- type class fails
  end

  variable (F)

  definition precategory_cone [instance] [constructor] : precategory (cone_obj F) :=
  @precategory.mk _ cone_hom
                 abstract begin
                   intro x y,
                   assert H : cone_hom x y ≃ Σ(f : x ⟶ y), Πi, cone_obj.η y i ∘ f = cone_obj.η x i,
                   { fapply equiv.MK,
                     { intro f, induction f, constructor, assumption},
                     { intro v, induction v, constructor, assumption},
                     { intro v, induction v, reflexivity},
                     { intro f, induction f, reflexivity}},
                   apply is_trunc.is_trunc_equiv_closed_rev, exact H,
                   fapply sigma.is_trunc_sigma, intros,
                   apply is_trunc_succ, apply pi.is_trunc_pi, intros, esimp,
                   /-exact _,-/ -- type class inference fails here
                   apply is_trunc_eq,
                 end end
                 (λx y z, cone_comp)
                 cone_id
                 abstract begin intros, apply cone_hom_eq, esimp, apply assoc    end end
                 abstract begin intros, apply cone_hom_eq, esimp, apply id_left  end end
                 abstract begin intros, apply cone_hom_eq, esimp, apply id_right end end

  definition cone [constructor] : Precategory :=
  precategory.Mk (precategory_cone F)

end category
