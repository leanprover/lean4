/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.functor
Author: Floris van Doorn
-/
import .basic
import logic.cast logic.funext
open function
open category eq eq.ops heq

structure functor (C D : Category) : Type :=
  (object : C → D)
  (morphism : Π⦃a b : C⦄, hom a b → hom (object a) (object b))
  (respect_id : Π (a : C), morphism (ID a) = ID (object a))
  (respect_comp : Π ⦃a b c : C⦄ (g : hom b c) (f : hom a b),
      morphism (g ∘ f) = morphism g ∘ morphism f)

infixl `⇒`:25 := functor

namespace functor
  attribute object [coercion]
  attribute morphism [coercion]
  attribute respect_id [irreducible]
  attribute respect_comp [irreducible]

  variables {A B C D : Category}

  protected definition compose [reducible] (G : functor B C) (F : functor A B) : functor A C :=
  functor.mk
    (λx, G (F x))
    (λ a b f, G (F f))
    (λ a, proof calc
      G (F (ID a)) = G id : {respect_id F a}
      --not giving the braces explicitly makes the elaborator compute a couple more seconds
               ... = id   : respect_id G (F a) qed)
    (λ a b c g f, proof calc
      G (F (g ∘ f)) = G (F g ∘ F f)     : respect_comp F g f
                ... = G (F g) ∘ G (F f) : respect_comp G (F g) (F f) qed)

  infixr `∘f`:60 := functor.compose

  protected theorem assoc (H : functor C D) (G : functor B C) (F : functor A B) :
      H ∘f (G ∘f F) = (H ∘f G) ∘f F :=
  rfl

  protected definition id [reducible] {C : Category} : functor C C :=
  mk (λa, a) (λ a b f, f) (λ a, rfl) (λ a b c f g, rfl)
  protected definition ID [reducible] (C : Category) : functor C C := @functor.id C

  protected theorem id_left  (F : functor C D) : (@functor.id D) ∘f F = F :=
  functor.rec (λ obF homF idF compF, dcongr_arg4 mk rfl rfl !proof_irrel !proof_irrel) F
  protected theorem id_right (F : functor C D) : F ∘f (@functor.id C) = F :=
  functor.rec (λ obF homF idF compF, dcongr_arg4 mk rfl rfl !proof_irrel !proof_irrel) F

end functor

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
    attribute category_of_categories [instance]
  end ops
end category

namespace functor

   variables {C D : Category}

  theorem mk_heq {obF obG : C → D} {homF homG idF idG compF compG} (Hob : ∀x, obF x = obG x)
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
    F

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
