-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn, Jakob von Raumer

import .functor hott.axioms.funext
open precategory path functor

inductive natural_transformation {C D : Precategory} (F G : C ⇒ D) : Type :=
mk : Π (η : Π (a : C), hom (F a) (G a))
  (nat : Π {a b : C} (f : hom a b), G f ∘ η a ≈ η b ∘ F f),
  natural_transformation F G

infixl `⟹`:25 := natural_transformation -- \==>

namespace natural_transformation
  variables {C D : Precategory} {F G H I : functor C D}

  definition natural_map [coercion] (η : F ⟹ G) : Π(a : C), F a ⟶ G a :=
  rec (λ x y, x) η

  theorem naturality (η : F ⟹ G) : Π⦃a b : C⦄ (f : a ⟶ b), G f ∘ η a ≈ η b ∘ F f :=
  rec (λ x y, y) η

  protected definition compose (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
  natural_transformation.mk
    (λ a, η a ∘ θ a)
    (λ a b f,
      calc
	H f ∘ (η a ∘ θ a) ≈ (H f ∘ η a) ∘ θ a : assoc
		      ... ≈(η b ∘ G f) ∘ θ a : naturality η f
		      ... ≈ η b ∘ (G f ∘ θ a) : assoc
		      ... ≈ η b ∘ (θ b ∘ F f) : naturality θ f
		      ... ≈ (η b ∘ θ b) ∘ F f : assoc)
--congr_arg (λx, η b ∘ x) (naturality θ f) -- this needed to be explicit for some reason (on Oct 24)

  infixr `∘n`:60 := compose

  definition foo (C : Precategory) (a b : C) (f g : hom a b) (p q : f ≈ g) : p ≈ q :=
  @truncation.is_hset.elim _ !homH f g p q

  protected definition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) [fext : funext.{l_1 l_4}] :
      η₃ ∘n (η₂ ∘n η₁) ≈ (η₃ ∘n η₂) ∘n η₁ :=
  dcongr_arg2 mk (funext.path_forall _ _ (λ x, !assoc)) sorry

  protected definition id {C D : Precategory} {F : functor C D} : natural_transformation F F :=
  mk (λa, id) (λa b f, !id_right ⬝ (!id_left⁻¹))
  protected definition ID {C D : Precategory} (F : functor C D) : natural_transformation F F := id

  protected theorem id_left (η : F ⟹ G) [fext : funext] : natural_transformation.compose id η ≈ η :=
  rec (λf H, path.dcongr_arg2 mk (funext.path_forall _ _ (λ x, !id_left)) sorry) η

  protected theorem id_right (η : F ⟹ G) [fext : funext] : natural_transformation.compose η id ≈ η :=
  rec (λf H, path.dcongr_arg2 mk (funext.path_forall _ _ (λ x, !id_right)) sorry) η
end natural_transformation
