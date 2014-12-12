-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn, Jakob von Raumer

import .functor types.pi
open eq precategory functor truncation equiv sigma.ops sigma is_equiv function pi

inductive natural_transformation {C D : Precategory} (F G : C ⇒ D) : Type :=
mk : Π (η : Π (a : C), hom (F a) (G a))
  (nat : Π {a b : C} (f : hom a b), G f ∘ η a = η b ∘ F f),
  natural_transformation F G

infixl `⟹`:25 := natural_transformation -- \==>

namespace natural_transformation
  variables {C D : Precategory} {F G H I : functor C D}

  definition natural_map [coercion] (η : F ⟹ G) : Π(a : C), F a ⟶ G a :=
  rec (λ x y, x) η

  theorem naturality (η : F ⟹ G) : Π⦃a b : C⦄ (f : a ⟶ b), G f ∘ η a = η b ∘ F f :=
  rec (λ x y, y) η

  protected definition sigma_char :
    (Σ (η : Π (a : C), hom (F a) (G a)), Π (a b : C) (f : hom a b), G f ∘ η a = η b ∘ F f) ≃ (F ⟹ G) :=
  /-equiv.mk (λ S, natural_transformation.mk S.1 S.2)
    (adjointify (λ S, natural_transformation.mk S.1 S.2)
      (λ H, natural_transformation.rec_on H (λ η nat, dpair η nat))
      (λ H, natural_transformation.rec_on H (λ η nat, idpath (natural_transformation.mk η nat)))
      (λ S, sigma.rec_on S (λ η nat, idpath (dpair η nat))))-/

  /- THE FOLLLOWING CAUSES LEAN TO SEGFAULT?
  begin
    fapply equiv.mk,
      intro S, apply natural_transformation.mk, exact (S.2),
    fapply adjointify,
        intro H, apply (natural_transformation.rec_on H), intros (η, natu),
        exact (dpair η @natu),
      intro H, apply (natural_transformation.rec_on _ _ _),
    intros,
  end
  check sigma_char-/
  sorry

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

  infixr `∘n`:60 := compose

  protected definition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) [fext fext2 fext3 : funext] :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  -- Proof broken, universe issues?
  /-have aux [visible] : is_hprop (Π (a b : C) (f : hom a b), I f ∘ (η₃ ∘n η₂) a ∘ η₁ a = ((η₃ ∘n η₂) b ∘ η₁ b) ∘ F f),
    begin
      repeat (apply trunc_pi; intros),
      apply (succ_is_trunc -1 (I a_2 ∘ (η₃ ∘n η₂) a ∘ η₁ a)),
    end,
  dcongr_arg2 mk (funext.path_forall _ _ (λ x, !assoc)) !is_hprop.elim-/
  sorry

  protected definition id {C D : Precategory} {F : functor C D} : natural_transformation F F :=
  mk (λa, id) (λa b f, !id_right ⬝ (!id_left⁻¹))
  protected definition ID {C D : Precategory} (F : functor C D) : natural_transformation F F := id

  protected definition id_left (η : F ⟹ G) [fext : funext.{l_1 l_4}] :
      id ∘n η = η :=
  --Proof broken like all trunc_pi proofs
  /-begin
    apply (rec_on η), intros (f, H),
    fapply (path.dcongr_arg2 mk),
      apply (funext.path_forall _ f (λa, !id_left)),
    assert (H1 : is_hprop (Π {a b : C} (g : hom a b), G g ∘ f a = f b ∘ F g)),
      --repeat (apply trunc_pi; intros),
      apply (@trunc_pi _ _ _ (-2 .+1) _),
    /-  apply (succ_is_trunc -1 (G a_2 ∘ f a) (f a_1 ∘ F a_2)),
    apply (!is_hprop.elim),-/
  end-/
  sorry

  protected definition id_right (η : F ⟹ G) [fext : funext.{l_1 l_4}] :
      η ∘n id = η :=
  --Proof broken like all trunc_pi proofs
  /-begin
    apply (rec_on η), intros (f, H),
    fapply (path.dcongr_arg2 mk),
      apply (funext.path_forall _ f (λa, !id_right)),
    assert (H1 : is_hprop (Π {a b : C} (g : hom a b), G g ∘ f a = f b ∘ F g)),
      repeat (apply trunc_pi; intros),
      apply (succ_is_trunc -1 (G a_2 ∘ f a) (f a_1 ∘ F a_2)),
    apply (!is_hprop.elim),
  end-/
  sorry

  protected definition to_hset [fx : funext] : is_hset (F ⟹ G) :=
  --Proof broken like all trunc_pi proofs
  /-begin
    apply trunc_equiv, apply (equiv.to_is_equiv sigma_char),
    apply trunc_sigma,
      apply trunc_pi, intro a, exact (@homH (objects D) _ (F a) (G a)),
    intro η, apply trunc_pi, intro a,
      apply trunc_pi, intro b, apply trunc_pi, intro f,
      apply succ_is_trunc, apply trunc_succ, exact (@homH (objects D) _ (F a) (G b)),
  end-/
  sorry

end natural_transformation
