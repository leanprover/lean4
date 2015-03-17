/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.precategory.nat_trans
Author: Floris van Doorn, Jakob von Raumer
-/

import .functor .iso
open eq category functor is_trunc equiv sigma.ops sigma is_equiv function pi funext iso

structure nat_trans {C D : Precategory} (F G : C ⇒ D) :=
 (natural_map : Π (a : C), hom (F a) (G a))
 (naturality : Π {a b : C} (f : hom a b), G f ∘ natural_map a = natural_map b ∘ F f)

namespace nat_trans

  infixl `⟹`:25 := nat_trans -- \==>
  variables {C D E : Precategory} {F G H I : C ⇒ D} {F' G' : D ⇒ E}

  attribute natural_map [coercion]

  protected definition compose [reducible] (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
  nat_trans.mk
    (λ a, η a ∘ θ a)
    (λ a b f,
      calc
        H f ∘ (η a ∘ θ a) = (H f ∘ η a) ∘ θ a : by rewrite assoc
                      ... = (η b ∘ G f) ∘ θ a : by rewrite naturality
                      ... = η b ∘ (G f ∘ θ a) : by rewrite assoc
                      ... = η b ∘ (θ b ∘ F f) : by rewrite naturality
                      ... = (η b ∘ θ b) ∘ F f : by rewrite assoc)

  infixr `∘n`:60 := compose

  protected definition id [reducible] {C D : Precategory} {F : functor C D} : nat_trans F F :=
  mk (λa, id) (λa b f, !id_right ⬝ !id_left⁻¹)

  protected definition ID [reducible] {C D : Precategory} (F : functor C D) : nat_trans F F :=
  id

  definition nat_trans_eq_mk' {η₁ η₂ : Π (a : C), hom (F a) (G a)}
    (nat₁ : Π (a b : C) (f : hom a b), G f ∘ η₁ a = η₁ b ∘ F f)
    (nat₂ : Π (a b : C) (f : hom a b), G f ∘ η₂ a = η₂ b ∘ F f)
    (p : η₁ ∼ η₂)
      : nat_trans.mk η₁ nat₁ = nat_trans.mk η₂ nat₂ :=
  apD011 nat_trans.mk (eq_of_homotopy p) !is_hprop.elim

  definition nat_trans_eq_mk {η₁ η₂ : F ⟹ G} : natural_map η₁ ∼ natural_map η₂ → η₁ = η₂ :=
  nat_trans.rec_on η₁ (λf₁ nat₁, nat_trans.rec_on η₂ (λf₂ nat₂ p, !nat_trans_eq_mk' p))

  protected definition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  nat_trans_eq_mk (λa, !assoc)

  protected definition id_left (η : F ⟹ G) : id ∘n η = η :=
  nat_trans_eq_mk (λa, !id_left)

  protected definition id_right (η : F ⟹ G) : η ∘n id = η :=
  nat_trans_eq_mk (λa, !id_right)

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
    intro η, apply nat_trans_eq_mk, intro a, apply idp,
    intro S,
    fapply sigma_eq,
      apply eq_of_homotopy, intro a,
      apply idp,
    apply is_hprop.elim,
  end

  set_option apply.class_instance false
  definition is_hset_nat_trans : is_hset (F ⟹ G) :=
  begin
    apply is_trunc_is_equiv_closed, apply (equiv.to_is_equiv !sigma_char),
    apply is_trunc_sigma,
      apply is_trunc_pi, intro a, exact (@homH (Precategory.carrier D) _ (F a) (G a)),
    intro η, apply is_trunc_pi, intro a,
    apply is_trunc_pi, intro b, apply is_trunc_pi, intro f,
    apply is_trunc_eq, apply is_trunc_succ, exact (@homH (Precategory.carrier D) _ (F a) (G b)),
  end

  definition nat_trans_functor_compose [reducible] (η : G ⟹ H) (F : E ⇒ C) : G ∘f F ⟹ H ∘f F :=
  nat_trans.mk
    (λ a, η (F a))
    (λ a b f, naturality η (F f))

  definition functor_nat_trans_compose [reducible] (F : D ⇒ E) (η : G ⟹ H) : F ∘f G ⟹ F ∘f H :=
  nat_trans.mk
    (λ a, F (η a))
    (λ a b f, calc
      F (H f) ∘ F (η a) = F (H f ∘ η a) : respect_comp
        ... = F (η b ∘ G f) : by rewrite (naturality η f)
        ... = F (η b) ∘ F (G f) : respect_comp)

  infixr `∘nf`:60 := nat_trans_functor_compose
  infixr `∘fn`:60 := functor_nat_trans_compose

  definition functor_nat_trans_compose_commute (η : F ⟹ G) (θ : F' ⟹ G')
    : (θ ∘nf G) ∘n (F' ∘fn η) = (G' ∘fn η) ∘n (θ ∘nf F) :=
  nat_trans_eq_mk (λc, (naturality θ (η c))⁻¹)

  definition nat_trans_of_eq [reducible] (p : F = G) : F ⟹ G :=
  nat_trans.mk (λc, hom_of_eq (ap010 to_fun_ob p c))
               (λa b f, eq.rec_on p (!id_right ⬝ !id_left⁻¹))
end nat_trans
