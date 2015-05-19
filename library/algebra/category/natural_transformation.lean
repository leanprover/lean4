/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.natural_transformation
Author: Floris van Doorn
-/

import .functor
open category eq eq.ops functor

inductive natural_transformation {C D : Category} (F G : C ⇒ D) : Type :=
mk : Π (η : Π(a : C), hom (F a) (G a)), (Π{a b : C} (f : hom a b), G f ∘ η a = η b ∘ F f)
 → natural_transformation F G

infixl `⟹`:25 := natural_transformation -- \==>

namespace natural_transformation
  variables {C D : Category} {F G H I : functor C D}

  definition natural_map [coercion] (η : F ⟹ G) : Π(a : C), F a ⟶ G a :=
  natural_transformation.rec (λ x y, x) η

  theorem naturality (η : F ⟹ G) : Π⦃a b : C⦄ (f : a ⟶ b), G f ∘ η a = η b ∘ F f :=
  natural_transformation.rec (λ x y, y) η

  protected definition compose (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
  natural_transformation.mk
    (λ a, η a ∘ θ a)
    (λ a b f,
      calc
        H f ∘ (η a ∘ θ a) = (H f ∘ η a) ∘ θ a : assoc
                      ... = (η b ∘ G f) ∘ θ a : naturality η f
                      ... = η b ∘ (G f ∘ θ a) : assoc
                      ... = η b ∘ (θ b ∘ F f) : naturality θ f
                      ... = (η b ∘ θ b) ∘ F f : assoc)
--congr_arg (λx, η b ∘ x) (naturality θ f) -- this needed to be explicit for some reason (on Oct 24)

  infixr `∘n`:60 := natural_transformation.compose
  protected theorem assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  dcongr_arg2 mk (funext (take x, !assoc)) !proof_irrel

  protected definition id {C D : Category} {F : functor C D} : natural_transformation F F :=
  mk (λa, id) (λa b f, !id_right ⬝ symm !id_left)
  protected definition ID {C D : Category} (F : functor C D) : natural_transformation F F := natural_transformation.id

  protected theorem id_left (η : F ⟹ G) : natural_transformation.compose natural_transformation.id η = η :=
  natural_transformation.rec (λf H, dcongr_arg2 mk (funext (take x, !id_left)) !proof_irrel) η

  protected theorem id_right (η : F ⟹ G) : natural_transformation.compose η natural_transformation.id = η :=
  natural_transformation.rec (λf H, dcongr_arg2 mk (funext (take x, !id_right)) !proof_irrel) η
end natural_transformation
