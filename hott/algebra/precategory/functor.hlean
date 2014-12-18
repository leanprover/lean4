-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Floris van Doorn, Jakob von Raumer

import .basic

open function precategory eq prod equiv is_equiv sigma sigma.ops

structure functor (C D : Precategory) : Type :=
  (obF : C → D)
  (homF : Π ⦃a b : C⦄, hom a b → hom (obF a) (obF b))
  (respect_id : Π (a : C), homF (ID a) = ID (obF a))
  (respect_comp : Π {a b c : C} (g : hom b c) (f : hom a b),
    homF (g ∘ f) = homF g ∘ homF f)

infixl `⇒`:25 := functor

namespace functor
  variables {C D E : Precategory}

  coercion [persistent] obF
  coercion [persistent] homF

  -- "functor C D" is equivalent to a certain sigma type
  set_option unifier.max_steps 38500
  protected definition sigma_char :
    (Σ   (obF : C → D)
    (homF : Π ⦃a b : C⦄, hom a b → hom (obF a) (obF b)),
    (Π (a : C), homF (ID a) = ID (obF a)) ×
    (Π {a b c : C} (g : hom b c) (f : hom a b),
      homF (g ∘ f) = homF g ∘ homF f)) ≃ (functor C D) :=
  begin
    fapply equiv.mk,
      intro S, fapply functor.mk,
        exact (S.1), exact (S.2.1),
        exact (pr₁ S.2.2), exact (pr₂ S.2.2),
    fapply adjointify,
      intro F, apply (functor.rec_on F), intros (d1, d2, d3, d4),
      exact (dpair d1 (dpair d2 (pair d3 (@d4)))),
    intro F, apply (functor.rec_on F), intros (d1, d2, d3, d4), apply idp,
    intro S, apply (sigma.rec_on S), intros (d1, S2),
    apply (sigma.rec_on S2), intros (d2, P1),
    apply (prod.rec_on P1), intros (d3, d4), apply idp,
  end

  protected definition compose (G : functor D E) (F : functor C D) : functor C E :=
  functor.mk
    (λx, G (F x))
    (λ a b f, G (F f))
    (λ a, calc
      G (F (ID a)) = G id : {respect_id F a} --not giving the braces explicitly makes the elaborator compute a couple more seconds
               ... = id   : respect_id G (F a))
    (λ a b c g f, calc
      G (F (g ∘ f)) = G (F g ∘ F f)     : respect_comp F g f
                ... = G (F g) ∘ G (F f) : respect_comp G (F g) (F f))

  infixr `∘f`:60 := compose


  protected theorem assoc {A B C D : Precategory} (H : functor C D) (G : functor B C) (F : functor A B) :
      H ∘f (G ∘f F) = (H ∘f G) ∘f F :=
  sorry

  /-protected definition id {C : Precategory} : functor C C :=
  mk (λa, a) (λ a b f, f) (λ a, idp) (λ a b c f g, idp)
  protected definition ID (C : Precategory) : functor C C := id

  protected theorem id_left  (F : functor C D) : id ∘f F = F :=
  functor.rec (λ obF homF idF compF, dcongr_arg4 mk idp idp !proof_irrel !proof_irrel) F
  protected theorem id_right (F : functor C D) : F ∘f id = F :=
  functor.rec (λ obF homF idF compF, dcongr_arg4 mk idp idp !proof_irrel !proof_irrel) F-/

end functor

/-
namespace category
  open functor
  definition category_of_categories [reducible] : category Category :=
  mk (λ a b, functor a b)
     (λ a b c g f, functor.compose g f)
     (λ a, functor.id)
     (λ a b c d h g f, !functor.assoc)
     (λ a b f, !functor.id_left)
     (λ a b f, !functor.id_right)
  definition Category_of_categories [reducible] := Mk category_of_categories

  namespace ops
    notation `Cat`:max := Category_of_categories
    instance [persistent] category_of_categories
  end ops
end category-/

namespace functor
--  open category.ops
--   universes l m
   variables {C D : Precategory}
--   check hom C D
--   variables (F : C ⟶ D) (G : D ⇒ C)
--   check G ∘ F
--   check F ∘f G
--   variables (a b : C) (f : a ⟶ b)
--   check F a
--   check F b
--   check F f
--   check G (F f)
--   print "---"
-- --  check (G ∘ F) f --error
--   check (λ(x : functor C C), x) (G ∘ F) f
--   check (G ∘f F) f
--   print "---"
-- --  check (G ∘ F) a --error
--   check (G ∘f F) a
--   print "---"
-- --  check λ(H : hom C D) (x : C), H x  --error
--   check λ(H : @hom _ Cat C D) (x : C), H x
--   check λ(H : C ⇒ D) (x : C), H x
--   print "---"
--   -- variables {obF obG : C → D} (Hob : ∀x, obF x = obG x) (homF : Π(a b : C) (f : a ⟶ b), obF a ⟶ obF b) (homG : Π(a b : C) (f : a ⟶ b), obG a ⟶ obG b)
-- --  check eq.rec_on (funext Hob) homF = homG

  /-theorem mk_heq {obF obG : C → D} {homF homG idF idG compF compG} (Hob : ∀x, obF x = obG x)
     (Hmor : ∀(a b : C) (f : a ⟶ b), homF a b f == homG a b f)
       : mk obF homF idF compF = mk obG homG idG compG :=
  hddcongr_arg4 mk
              (funext Hob)
              (hfunext (λ a, hfunext (λ b, hfunext (λ f, !Hmor))))
              !proof_irrel
              !proof_irrel

  protected theorem hequal {F G : C ⇒ D} : Π (Hob : ∀x, F x = G x)
      (Hmor : ∀a b (f : a ⟶ b), F f == G f), F = G :=
  functor.rec
    (λ obF homF idF compF,
      functor.rec
        (λ obG homG idG compG Hob Hmor, mk_heq Hob Hmor)
      G)
    F-/

--   theorem mk_eq {obF obG : C → D} {homF homG idF idG compF compG} (Hob : ∀x, obF x = obG x)
--      (Hmor : ∀(a b : C) (f : a ⟶ b), cast (congr_arg (λ x, x a ⟶ x b) (funext Hob)) (homF a b f)
--                                        = homG a b f)
--        : mk obF homF idF compF = mk obG homG idG compG :=
--   dcongr_arg4 mk
--               (funext Hob)
--               (funext (λ a, funext (λ b, funext (λ f, sorry ⬝ Hmor a b f))))
-- -- to fill this sorry use (a generalization of) cast_pull
--               !proof_irrel
--               !proof_irrel

--   protected theorem equal {F G : C ⇒ D} : Π (Hob : ∀x, F x = G x)
--       (Hmor : ∀a b (f : a ⟶ b), cast (congr_arg (λ x, x a ⟶ x b) (funext Hob)) (F f) = G f), F = G :=
--   functor.rec
--     (λ obF homF idF compF,
--       functor.rec
--         (λ obG homG idG compG Hob Hmor, mk_eq Hob Hmor)
--       G)
--     F


end functor
