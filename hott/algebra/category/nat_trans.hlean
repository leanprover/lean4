/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn, Jakob von Raumer
-/
import .functor .iso
open eq category functor is_trunc equiv sigma.ops sigma is_equiv function pi funext iso

structure nat_trans {C D : Precategory} (F G : C ⇒ D) :=
 (natural_map : Π (a : C), hom (F a) (G a))
 (naturality : Π {a b : C} (f : hom a b), G f ∘ natural_map a = natural_map b ∘ F f)

namespace nat_trans

  infixl `⟹`:25 := nat_trans -- \==>
  variables {B C D E : Precategory} {F G H I : C ⇒ D} {F' G' : D ⇒ E}

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

  infixr `∘n`:60 := nat_trans.compose

  protected definition id [reducible] {C D : Precategory} {F : functor C D} : nat_trans F F :=
  mk (λa, id) (λa b f, !id_right ⬝ !id_left⁻¹)

  protected definition ID [reducible] {C D : Precategory} (F : functor C D) : nat_trans F F :=
  (@nat_trans.id C D F)

  definition nat_trans_mk_eq {η₁ η₂ : Π (a : C), hom (F a) (G a)}
    (nat₁ : Π (a b : C) (f : hom a b), G f ∘ η₁ a = η₁ b ∘ F f)
    (nat₂ : Π (a b : C) (f : hom a b), G f ∘ η₂ a = η₂ b ∘ F f)
    (p : η₁ ∼ η₂)
      : nat_trans.mk η₁ nat₁ = nat_trans.mk η₂ nat₂ :=
  apd011 nat_trans.mk (eq_of_homotopy p) !is_hprop.elim

  definition nat_trans_eq {η₁ η₂ : F ⟹ G} : natural_map η₁ ∼ natural_map η₂ → η₁ = η₂ :=
  nat_trans.rec_on η₁ (λf₁ nat₁, nat_trans.rec_on η₂ (λf₂ nat₂ p, !nat_trans_mk_eq p))

  protected definition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  nat_trans_eq (λa, !assoc)

  protected definition id_left (η : F ⟹ G) : nat_trans.id ∘n η = η :=
  nat_trans_eq (λa, !id_left)

  protected definition id_right (η : F ⟹ G) : η ∘n nat_trans.id = η :=
  nat_trans_eq (λa, !id_right)

  protected definition sigma_char (F G : C ⇒ D) :
    (Σ (η : Π (a : C), hom (F a) (G a)), Π (a b : C) (f : hom a b), G f ∘ η a = η b ∘ F f) ≃  (F ⟹ G) :=
  begin
    fapply equiv.mk,
      -- TODO(Leo): investigate why we need to use rexact in the following line
      {intro S, apply nat_trans.mk, rexact (S.2)},
    fapply adjointify,
      intro H,
          fapply sigma.mk,
            intro a, exact (H a),
          intro a b f, exact (naturality H f),
    intro η, apply nat_trans_eq, intro a, apply idp,
    intro S,
    fapply sigma_eq,
    { apply eq_of_homotopy, intro a, apply idp},
    { apply is_hprop.elimo}
  end

  definition is_hset_nat_trans [instance] : is_hset (F ⟹ G) :=
  by apply is_trunc_is_equiv_closed; apply (equiv.to_is_equiv !nat_trans.sigma_char)

  definition nat_trans_functor_compose [reducible] (η : G ⟹ H) (F : E ⇒ C) : G ∘f F ⟹ H ∘f F :=
  nat_trans.mk
    (λ a, η (F a))
    (λ a b f, naturality η (F f))

  definition functor_nat_trans_compose [reducible] (F : D ⇒ E) (η : G ⟹ H) : F ∘f G ⟹ F ∘f H :=
  nat_trans.mk
    (λ a, F (η a))
    (λ a b f, calc
      F (H f) ∘ F (η a) = F (H f ∘ η a) : by rewrite respect_comp
        ... = F (η b ∘ G f)             : by rewrite (naturality η f)
        ... = F (η b) ∘ F (G f)         : by rewrite respect_comp)

  infixr `∘nf`:62 := nat_trans_functor_compose
  infixr `∘fn`:62 := functor_nat_trans_compose

  definition nf_fn_eq_fn_nf_pt (η : F ⟹ G) (θ : F' ⟹ G') (c : C)
    : (θ (G c)) ∘ (F' (η c)) = (G' (η c)) ∘ (θ (F c)) :=
  (naturality θ (η c))⁻¹

  definition nf_fn_eq_fn_nf (η : F ⟹ G) (θ : F' ⟹ G')
    : (θ ∘nf G) ∘n (F' ∘fn η) = (G' ∘fn η) ∘n (θ ∘nf F) :=
  nat_trans_eq (λc, !nf_fn_eq_fn_nf_pt)

  definition fn_n_distrib (F' : D ⇒ E) (η : G ⟹ H) (θ : F ⟹ G)
    : F' ∘fn (η ∘n θ) = (F' ∘fn η) ∘n (F' ∘fn θ) :=
  nat_trans_eq (λc, !respect_comp)

  definition n_nf_distrib (η : G ⟹ H) (θ : F ⟹ G) (F' : B ⇒ C)
    : (η ∘n θ) ∘nf F' = (η ∘nf F') ∘n (θ ∘nf F') :=
  nat_trans_eq (λc, idp)

  definition fn_id (F' : D ⇒ E) : F' ∘fn nat_trans.ID F = nat_trans.id :=
  nat_trans_eq (λc, !respect_id)

  definition id_nf (F' : B ⇒ C) : nat_trans.ID F ∘nf F' = nat_trans.id :=
  nat_trans_eq (λc, idp)

  definition id_fn (η : G ⟹ H) (c : C) : (functor.id ∘fn η) c = η c :=
  idp

  definition nf_id (η : G ⟹ H) (c : C) : (η ∘nf functor.id) c = η c :=
  idp

  definition nat_trans_of_eq [reducible] (p : F = G) : F ⟹ G :=
  nat_trans.mk (λc, hom_of_eq (ap010 to_fun_ob p c))
               (λa b f, eq.rec_on p (!id_right ⬝ !id_left⁻¹))
end nat_trans
