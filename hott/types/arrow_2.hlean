/-
Copyright (c) 2015 Ulrik Buchholtz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ulrik Buchholtz
-/

import ..function

open eq is_equiv function

namespace arrow

  structure arrow :=
    (dom : Type)
    (cod : Type)
    (arrow : dom → cod)

  abbreviation dom [unfold 2] := @arrow.dom
  abbreviation cod [unfold 2] := @arrow.cod

  definition arrow_of_fn {A B : Type} (f : A → B) : arrow :=
  arrow.mk A B f

  structure morphism (A B : Type) :=
    (mor : A → B)

  definition morphism_of_arrow [coercion] (f : arrow) : morphism (dom f) (cod f) :=
  morphism.mk (arrow.arrow f)

  attribute morphism.mor [coercion]

  structure arrow_hom (f g : arrow) :=
    (on_dom : dom f → dom g)
    (on_cod : cod f → cod g)
    (commute : Π(x : dom f), g (on_dom x) = on_cod (f x))

  abbreviation on_dom [unfold 2] := @arrow_hom.on_dom
  abbreviation on_cod [unfold 2] := @arrow_hom.on_cod
  abbreviation commute [unfold 2] := @arrow_hom.commute

  variables {f g : arrow}

  definition on_fiber [reducible] (r : arrow_hom f g) (y : cod f)
    : fiber f y → fiber g (on_cod r y) :=
  fiber.rec (λx p, fiber.mk (on_dom r x) (commute r x ⬝ ap (on_cod r) p))

  structure is_retraction [class] (r : arrow_hom f g) : Type :=
    (sect : arrow_hom g f)
    (right_inverse_dom : Π(a : dom g), on_dom r (on_dom sect a) = a)
    (right_inverse_cod : Π(b : cod g), on_cod r (on_cod sect b) = b)
    (cohere : Π(a : dom g), commute r (on_dom sect a) ⬝ ap (on_cod r) (commute sect a)
                            = ap g (right_inverse_dom a) ⬝ (right_inverse_cod (g a))⁻¹)

  definition retraction_on_fiber [reducible] (r : arrow_hom f g) [H : is_retraction r]
    (b : cod g) : fiber f (on_cod (is_retraction.sect r) b) → fiber g b :=
  fiber.rec (λx q, fiber.mk (on_dom r x) (commute r x ⬝ ap (on_cod r) q ⬝ is_retraction.right_inverse_cod r b))

  definition retraction_on_fiber_right_inverse' (r : arrow_hom f g) [H : is_retraction r]
    (a : dom g) (b : cod g) (p : g a = b)
    : retraction_on_fiber r b (on_fiber (is_retraction.sect r) b (fiber.mk a p)) = fiber.mk a p :=
  begin
    induction p, unfold on_fiber, unfold retraction_on_fiber,
    apply @fiber.fiber_eq _ _ g (g a)
      (fiber.mk
        (on_dom r (on_dom (is_retraction.sect r) a))
        (commute r (on_dom (is_retraction.sect r) a)
          ⬝ ap (on_cod r) (commute (is_retraction.sect r) a)
          ⬝ is_retraction.right_inverse_cod r (g a)))
      (fiber.mk a (refl (g a)))
      (is_retraction.right_inverse_dom r a), -- everything but this field should be inferred
    unfold fiber.point_eq,
    rewrite [is_retraction.cohere r a],
    apply inv_con_cancel_right
  end

  definition retraction_on_fiber_right_inverse (r : arrow_hom f g) [H : is_retraction r]
    : Π(b : cod g), Π(z : fiber g b), retraction_on_fiber r b (on_fiber (is_retraction.sect r) b z) = z :=
  λb, fiber.rec (λa p, retraction_on_fiber_right_inverse' r a b p)

  -- Lemma 4.7.3
  definition retraction_on_fiber_is_retraction [instance] (r : arrow_hom f g) [H : is_retraction r]
    (b : cod g) : _root_.is_retraction (retraction_on_fiber r b) :=
  _root_.is_retraction.mk (on_fiber (is_retraction.sect r) b) (retraction_on_fiber_right_inverse r b)

  -- Theorem 4.7.4
  definition retract_of_equivalence_is_equivalence (r : arrow_hom f g) [H : is_retraction r]
    [K : is_equiv f] : is_equiv g :=
  begin
    apply @is_equiv_of_is_contr_fun _ _ g,
    intro b,
    apply is_contr_retract (retraction_on_fiber r b),
    exact is_contr_fun_of_is_equiv f (on_cod (is_retraction.sect r) b)
  end

end arrow

namespace arrow
  variables {A B : Type} {f g : A → B} (p : f ~ g)

  definition arrow_hom_of_homotopy : arrow_hom (arrow_of_fn f) (arrow_of_fn g) :=
  arrow_hom.mk id id (λx, (p x)⁻¹)

  definition is_retraction_arrow_hom_of_homotopy [instance]
    : is_retraction (arrow_hom_of_homotopy p) :=
  is_retraction.mk
    (arrow_hom_of_homotopy (λx, (p x)⁻¹))
    (λa, idp)
    (λb, idp)
    (λa, con_eq_of_eq_inv_con (ap_id _))

end arrow
