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

  definition natural_map [coercion] (η : F ⟹ G) : Π (a : C), F a ⟶ G a :=
  rec (λ x y, x) η

  theorem naturality (η : F ⟹ G) : Π⦃a b : C⦄ (f : a ⟶ b), G f ∘ η a = η b ∘ F f :=
  rec (λ x y, y) η

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

  infixr `∘n`:60 := compose

  protected theorem congr
    {C : Precategory} {D : Precategory}
    (F G : C ⇒ D)
    (η₁ η₂ : Π (a : C), hom (F a) (G a))
    (nat₁ : Π (a b : C) (f : hom a b), G f ∘ η₁ a = η₁ b ∘ F f)
    (nat₂ : Π (a b : C) (f : hom a b), G f ∘ η₂ a = η₂ b ∘ F f)
    (p₁ : η₁ = η₂) (p₂ : p₁ ▹ nat₁ = nat₂)
    : @natural_transformation.mk C D F G η₁ nat₁ = @natural_transformation.mk C D F G η₂ nat₂
  :=
  begin
    apply (dcongr_arg2 (@natural_transformation.mk C D F G) p₁ p₂),
  end


  protected definition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  begin
    apply (rec_on η₃), intros (η₃1, η₃2),
    apply (rec_on η₂), intros (η₂1, η₂2),
    apply (rec_on η₁), intros (η₁1, η₁2),
    fapply natural_transformation.congr,
      apply funext.path_pi, intro a,
      apply assoc,
    apply funext.path_pi, intro a,
    apply funext.path_pi, intro b,
    apply funext.path_pi, intro f,
    apply (@is_hset.elim), apply !homH,
  end

  protected definition id {C D : Precategory} {F : functor C D} : natural_transformation F F :=
  mk (λa, id) (λa b f, !id_right ⬝ (!id_left⁻¹))

  protected definition ID {C D : Precategory} (F : functor C D) : natural_transformation F F :=
  id

  protected definition id_left (η : F ⟹ G) : id ∘n η = η :=
  begin
    apply (rec_on η), intros (η₁, nat₁),
    fapply (natural_transformation.congr F G),
      apply funext.path_pi, intro a,
      apply id_left,
    apply funext.path_pi, intro a,
    apply funext.path_pi, intro b,
    apply funext.path_pi, intro f,
    apply (@is_hset.elim), apply !homH,
  end

  protected definition id_right (η : F ⟹ G) : η ∘n id = η :=
  begin
    apply (rec_on η), intros (η₁, nat₁),
    fapply (natural_transformation.congr F G),
      apply funext.path_pi, intro a,
      apply id_right,
    apply funext.path_pi, intro a,
    apply funext.path_pi, intro b,
    apply funext.path_pi, intro f,
    apply (@is_hset.elim), apply !homH,
  end

  --set_option pp.implicit true
  protected definition sigma_char (F G : C ⇒ D) :
    (Σ (η : Π (a : C), hom (F a) (G a)), Π (a b : C) (f : hom a b), G f ∘ η a = η b ∘ F f) ≃  (F ⟹ G) :=
  begin
    fapply equiv.mk,
      intro S, apply natural_transformation.mk, exact (S.2),
    fapply adjointify,
      intro H,
          fapply sigma.mk,
            intro a, exact (H a),
          intros (a, b, f), exact (naturality H f),
    intro H, apply (natural_transformation.rec_on H),
    intros (eta, nat), unfold function.id,
    fapply natural_transformation.congr,
        apply idp,
      repeat ( apply funext.path_pi ; intro a ),
      apply (@is_hset.elim), apply !homH,
    intro S,
    fapply sigma.path,
      apply funext.path_pi, intro a,
      apply idp,
    repeat ( apply funext.path_pi ; intro a ),
    apply (@is_hset.elim), apply !homH,
  end

  protected definition to_hset : is_hset (F ⟹ G) :=
  begin
    apply trunc_equiv, apply (equiv.to_is_equiv !sigma_char),
    apply trunc_sigma,
      apply trunc_pi, intro a, exact (@homH (objects D) _ (F a) (G a)),
    intro η, apply trunc_pi, intro a,
    apply trunc_pi, intro b, apply trunc_pi, intro f,
    apply succ_is_trunc, apply trunc_succ, exact (@homH (objects D) _ (F a) (G b)),
  end

end natural_transformation
