-- Copyright (c) 2014 Floris van Doorn. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Floris van Doorn, Jakob von Raumer

import .functor
open eq precategory functor is_trunc equiv sigma.ops sigma is_equiv function pi

inductive nat_trans {C D : Precategory} (F G : C ⇒ D) : Type :=
mk : Π (η : Π (a : C), hom (F a) (G a))
  (nat : Π {a b : C} (f : hom a b), G f ∘ η a = η b ∘ F f),
  nat_trans F G

infixl `⟹`:25 := nat_trans -- \==>

namespace nat_trans
  variables {C D : Precategory} {F G H I : functor C D}

  definition natural_map [coercion] (η : F ⟹ G) : Π (a : C), F a ⟶ G a :=
  nat_trans.rec (λ x y, x) η

  theorem naturality (η : F ⟹ G) : Π⦃a b : C⦄ (f : a ⟶ b), G f ∘ η a = η b ∘ F f :=
  nat_trans.rec (λ x y, y) η

  protected definition compose (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
  nat_trans.mk
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
    : @nat_trans.mk C D F G η₁ nat₁ = @nat_trans.mk C D F G η₂ nat₂
  :=
  begin
    apply (apD011 (@nat_trans.mk C D F G) p₁ p₂),
  end

  set_option apply.class_instance false -- disable class instance resolution in the apply tactic

  protected definition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  begin
    apply (nat_trans.rec_on η₃), intros (η₃1, η₃2),
    apply (nat_trans.rec_on η₂), intros (η₂1, η₂2),
    apply (nat_trans.rec_on η₁), intros (η₁1, η₁2),
    fapply nat_trans.congr,
      apply funext.eq_of_homotopy, intro a,
      apply assoc,
    apply funext.eq_of_homotopy, intro a,
    apply funext.eq_of_homotopy, intro b,
    apply funext.eq_of_homotopy, intro f,
    apply (@is_hset.elim), apply !homH,
  end

  protected definition id {C D : Precategory} {F : functor C D} : nat_trans F F :=
  mk (λa, id) (λa b f, !id_right ⬝ (!id_left⁻¹))

  protected definition ID {C D : Precategory} (F : functor C D) : nat_trans F F :=
  id

  protected definition id_left (η : F ⟹ G) : id ∘n η = η :=
  begin
    apply (nat_trans.rec_on η), intros (η₁, nat₁),
    fapply (nat_trans.congr F G),
      apply funext.eq_of_homotopy, intro a,
      apply id_left,
    apply funext.eq_of_homotopy, intro a,
    apply funext.eq_of_homotopy, intro b,
    apply funext.eq_of_homotopy, intro f,
    apply (@is_hset.elim), apply !homH,
  end

  protected definition id_right (η : F ⟹ G) : η ∘n id = η :=
  begin
    apply (nat_trans.rec_on η), intros (η₁, nat₁),
    fapply (nat_trans.congr F G),
      apply funext.eq_of_homotopy, intro a,
      apply id_right,
    apply funext.eq_of_homotopy, intro a,
    apply funext.eq_of_homotopy, intro b,
    apply funext.eq_of_homotopy, intro f,
    apply (@is_hset.elim), apply !homH,
  end

  --set_option pp.implicit true
  protected definition sigma_char (F G : C ⇒ D) :
    (Σ (η : Π (a : C), hom (F a) (G a)), Π (a b : C) (f : hom a b), G f ∘ η a = η b ∘ F f) ≃  (F ⟹ G) :=
  begin
    fapply equiv.mk,
      intro S, apply nat_trans.mk, exact (S.2),
    fapply adjointify,
      intro H,
          fapply sigma.mk,
            intro a, exact (H a),
          intros (a, b, f), exact (naturality H f),
    intro H, apply (nat_trans.rec_on H),
    intros (eta, nat), unfold function.id,
    fapply nat_trans.congr,
        apply idp,
      repeat ( apply funext.eq_of_homotopy ; intro a ),
      apply (@is_hset.elim), apply !homH,
    intro S,
    fapply sigma_eq,
      apply funext.eq_of_homotopy, intro a,
      apply idp,
    repeat ( apply funext.eq_of_homotopy ; intro a ),
    apply (@is_hset.elim), apply !homH,
  end

  protected definition to_hset : is_hset (F ⟹ G) :=
  begin
    apply is_trunc_is_equiv_closed, apply (equiv.to_is_equiv !sigma_char),
    apply is_trunc_sigma,
      apply is_trunc_pi, intro a, exact (@homH (objects D) _ (F a) (G a)),
    intro η, apply is_trunc_pi, intro a,
    apply is_trunc_pi, intro b, apply is_trunc_pi, intro f,
    apply is_trunc_eq, apply is_trunc_succ, exact (@homH (objects D) _ (F a) (G b)),
  end

end nat_trans
