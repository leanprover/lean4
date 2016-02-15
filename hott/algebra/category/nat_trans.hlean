/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn, Jakob von Raumer
-/

import .functor.basic
open eq category functor is_trunc equiv sigma.ops sigma is_equiv function pi funext iso

structure nat_trans {C : Precategory} {D : Precategory} (F G : C ⇒ D)
  : Type :=
 (natural_map : Π (a : C), hom (F a) (G a))
 (naturality : Π {a b : C} (f : hom a b), G f ∘ natural_map a = natural_map b ∘ F f)

namespace nat_trans

  infixl ` ⟹ `:25 := nat_trans -- \==>
  variables {B C D E : Precategory} {F G H I : C ⇒ D} {F' G' : D ⇒ E} {F'' G'' : E ⇒ B} {J : C ⇒ C}

  attribute natural_map [coercion]

  protected definition compose [constructor] (η : G ⟹ H) (θ : F ⟹ G) : F ⟹ H :=
  nat_trans.mk
    (λ a, η a ∘ θ a)
    (λ a b f,
      abstract calc
        H f ∘ (η a ∘ θ a) = (H f ∘ η a) ∘ θ a : by rewrite assoc
                      ... = (η b ∘ G f) ∘ θ a : by rewrite naturality
                      ... = η b ∘ (G f ∘ θ a) : by rewrite assoc
                      ... = η b ∘ (θ b ∘ F f) : by rewrite naturality
                      ... = (η b ∘ θ b) ∘ F f : by rewrite assoc
      end)

  infixr ` ∘n `:60 := nat_trans.compose

  definition compose_def (η : G ⟹ H) (θ : F ⟹ G) (c : C) : (η ∘n θ) c = η c ∘ θ c := idp

  protected definition id [reducible] [constructor] {F : C ⇒ D} : nat_trans F F :=
  mk (λa, id) (λa b f, !id_right ⬝ !id_left⁻¹)

  protected definition ID [reducible] [constructor] (F : C ⇒ D) : nat_trans F F :=
  (@nat_trans.id C D F)

  notation 1 := nat_trans.id

  definition constant_nat_trans [constructor] (C : Precategory) {D : Precategory} {d d' : D}
    (g : d ⟶ d') : constant_functor C d ⟹ constant_functor C d' :=
  mk (λc, g) (λc c' f, !id_comp_eq_comp_id)

  definition nat_trans_mk_eq {η₁ η₂ : Π (a : C), hom (F a) (G a)}
    (nat₁ : Π (a b : C) (f : hom a b), G f ∘ η₁ a = η₁ b ∘ F f)
    (nat₂ : Π (a b : C) (f : hom a b), G f ∘ η₂ a = η₂ b ∘ F f)
    (p : η₁ ~ η₂)
      : nat_trans.mk η₁ nat₁ = nat_trans.mk η₂ nat₂ :=
  apd011 nat_trans.mk (eq_of_homotopy p) !is_prop.elim

  definition nat_trans_eq {η₁ η₂ : F ⟹ G} : natural_map η₁ ~ natural_map η₂ → η₁ = η₂ :=
  by induction η₁; induction η₂; apply nat_trans_mk_eq

  protected definition assoc (η₃ : H ⟹ I) (η₂ : G ⟹ H) (η₁ : F ⟹ G) :
      η₃ ∘n (η₂ ∘n η₁) = (η₃ ∘n η₂) ∘n η₁ :=
  nat_trans_eq (λa, !assoc)

  protected definition id_left (η : F ⟹ G) : 1 ∘n η = η :=
  nat_trans_eq (λa, !id_left)

  protected definition id_right (η : F ⟹ G) : η ∘n 1 = η :=
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
    { apply is_prop.elimo}
  end

  definition is_set_nat_trans [instance] : is_set (F ⟹ G) :=
  by apply is_trunc_is_equiv_closed; apply (equiv.to_is_equiv !nat_trans.sigma_char)

  definition change_natural_map [constructor] (η : F ⟹ G) (f : Π (a : C), F a ⟶ G a)
    (p : Πa, η a = f a) : F ⟹ G :=
  nat_trans.mk f (λa b g, p a ▸ p b ▸ naturality η g)

  definition nat_trans_functor_compose [constructor] (η : G ⟹ H) (F : E ⇒ C)
    : G ∘f F ⟹ H ∘f F :=
  nat_trans.mk
    (λ a, η (F a))
    (λ a b f, naturality η (F f))

  definition functor_nat_trans_compose [constructor] (F : D ⇒ E) (η : G ⟹ H)
    : F ∘f G ⟹ F ∘f H :=
  nat_trans.mk
    (λ a, F (η a))
    (λ a b f, calc
      F (H f) ∘ F (η a) = F (H f ∘ η a) : by rewrite respect_comp
        ... = F (η b ∘ G f)             : by rewrite (naturality η f)
        ... = F (η b) ∘ F (G f)         : by rewrite respect_comp)

  definition nat_trans_id_functor_compose [constructor] (η : J ⟹ 1) (F : E ⇒ C)
    : J ∘f F ⟹ F :=
  nat_trans.mk
    (λ a, η (F a))
    (λ a b f, naturality η (F f))

  definition id_nat_trans_functor_compose [constructor] (η : 1 ⟹ J) (F : E ⇒ C)
    : F ⟹ J ∘f F :=
  nat_trans.mk
    (λ a, η (F a))
    (λ a b f, naturality η (F f))

  definition functor_nat_trans_id_compose [constructor] (F : C ⇒ D) (η : J ⟹ 1)
    : F ∘f J ⟹ F :=
  nat_trans.mk
    (λ a, F (η a))
    (λ a b f, calc
      F f ∘ F (η a) = F (f ∘ η a) : by rewrite respect_comp
        ... = F (η b ∘ J f)       : by rewrite (naturality η f)
        ... = F (η b) ∘ F (J f)   : by rewrite respect_comp)

  definition functor_id_nat_trans_compose [constructor] (F : C ⇒ D) (η : 1 ⟹ J)
    : F ⟹ F ∘f J :=
  nat_trans.mk
    (λ a, F (η a))
    (λ a b f, calc
      F (J f) ∘ F (η a) = F (J f ∘ η a) : by rewrite respect_comp
        ... = F (η b ∘ f)               : by rewrite (naturality η f)
        ... = F (η b) ∘ F f             : by rewrite respect_comp)

  infixr ` ∘nf ` :62 := nat_trans_functor_compose
  infixr ` ∘fn ` :62 := functor_nat_trans_compose
  infixr ` ∘n1f `:62 := nat_trans_id_functor_compose
  infixr ` ∘1nf `:62 := id_nat_trans_functor_compose
  infixr ` ∘f1n `:62 := functor_id_nat_trans_compose
  infixr ` ∘fn1 `:62 := functor_nat_trans_id_compose

  definition nf_fn_eq_fn_nf_pt (η : F ⟹ G) (θ : F' ⟹ G') (c : C)
    : (θ (G c)) ∘ (F' (η c)) = (G' (η c)) ∘ (θ (F c)) :=
  (naturality θ (η c))⁻¹

  variable (F')
  definition nf_fn_eq_fn_nf_pt' (η : F ⟹ G) (θ : F'' ⟹ G'') (c : C)
    : (θ (F' (G c))) ∘ (F'' (F' (η c))) = (G'' (F' (η c))) ∘ (θ (F' (F c))) :=
  (naturality θ (F' (η c)))⁻¹
  variable {F'}

  definition nf_fn_eq_fn_nf (η : F ⟹ G) (θ : F' ⟹ G')
    : (θ ∘nf G) ∘n (F' ∘fn η) = (G' ∘fn η) ∘n (θ ∘nf F) :=
  nat_trans_eq (λ c, nf_fn_eq_fn_nf_pt η θ c)

  definition fn_n_distrib (F' : D ⇒ E) (η : G ⟹ H) (θ : F ⟹ G)
    : F' ∘fn (η ∘n θ) = (F' ∘fn η) ∘n (F' ∘fn θ) :=
  nat_trans_eq (λc, by apply respect_comp)

  definition n_nf_distrib (η : G ⟹ H) (θ : F ⟹ G) (F' : B ⇒ C)
    : (η ∘n θ) ∘nf F' = (η ∘nf F') ∘n (θ ∘nf F') :=
  nat_trans_eq (λc, idp)

  definition fn_id (F' : D ⇒ E) : F' ∘fn nat_trans.ID F = 1 :=
  nat_trans_eq (λc, by apply respect_id)

  definition id_nf (F' : B ⇒ C) : nat_trans.ID F ∘nf F' = 1 :=
  nat_trans_eq (λc, idp)

  definition id_fn (η : G ⟹ H) (c : C) : (1 ∘fn η) c = η c :=
  idp

  definition nf_id (η : G ⟹ H) (c : C) : (η ∘nf 1) c = η c :=
  idp

  definition nat_trans_of_eq [reducible] [constructor] (p : F = G) : F ⟹ G :=
  nat_trans.mk (λc, hom_of_eq (ap010 to_fun_ob p c))
               (λa b f, eq.rec_on p (!id_right ⬝ !id_left⁻¹))

  definition compose_rev [unfold_full] (θ : F ⟹ G) (η : G ⟹ H) : F ⟹ H := η ∘n θ

end nat_trans

attribute nat_trans.compose_rev [trans]
attribute nat_trans.id [refl]
