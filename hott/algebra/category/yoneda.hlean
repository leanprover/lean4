/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Yoneda embedding and Yoneda lemma
-/

import .curry .constructions.hset .constructions.opposite .adjoint

open category eq functor prod.ops is_trunc iso is_equiv equiv category.set nat_trans lift

namespace yoneda

  definition representable_functor_assoc [C : Precategory] {a1 a2 a3 a4 a5 a6 : C}
    (f1 : hom a5 a6) (f2 : hom a4 a5) (f3 : hom a3 a4) (f4 : hom a2 a3) (f5 : hom a1 a2)
      : (f1 ∘ f2) ∘ f3 ∘ (f4 ∘ f5) = f1 ∘ (f2 ∘ f3 ∘ f4) ∘ f5 :=
  calc
        _ = f1 ∘ f2 ∘ f3 ∘ f4 ∘ f5     : by rewrite -assoc
      ... = f1 ∘ (f2 ∘ f3) ∘ f4 ∘ f5   : by rewrite -assoc
      ... = f1 ∘ ((f2 ∘ f3) ∘ f4) ∘ f5 : by rewrite -(assoc (f2 ∘ f3) _ _)
      ... = _                          : by rewrite (assoc f2 f3 f4)

  definition hom_functor.{u v} [constructor] (C : Precategory.{u v}) : Cᵒᵖ ×c C ⇒ cset.{v} :=
  functor.mk
    (λ (x : Cᵒᵖ ×c C), @homset (Cᵒᵖ) C x.1 x.2)
    (λ (x y : Cᵒᵖ ×c C) (f : @category.precategory.hom (Cᵒᵖ ×c C) (Cᵒᵖ ×c C) x y) (h : @homset (Cᵒᵖ) C x.1 x.2),
       f.2 ∘[C] (h ∘[C] f.1))
    (λ x, @eq_of_homotopy _ _ _ (ID (@homset Cᵒᵖ C x.1 x.2)) (λ h, concat (by apply @id_left) (by apply @id_right)))
    (λ x y z g f,
       eq_of_homotopy (by intros; apply @representable_functor_assoc))

  /-
    These attributes make sure that the fields of the category "set" reduce to the right things
    However, we don't want to have them globally, because that will unfold the composition g ∘ f
    in a Category to category.category.comp g f
  -/
  local attribute Category.to.precategory category.to_precategory [constructor]

  -- should this be defined as "yoneda_embedding Cᵒᵖ"?
  definition contravariant_yoneda_embedding [reducible] (C : Precategory) : Cᵒᵖ ⇒ cset ^c C :=
  functor_curry !hom_functor

  definition yoneda_embedding (C : Precategory) : C ⇒ cset ^c Cᵒᵖ :=
  functor_curry (!hom_functor ∘f !functor_prod_flip)

  notation `ɏ` := yoneda_embedding _

  definition yoneda_lemma_hom [constructor] {C : Precategory} (c : C) (F : Cᵒᵖ ⇒ cset)
    (x : trunctype.carrier (F c)) : ɏ c ⟹ F :=
  begin
    fapply nat_trans.mk,
    { intro c', esimp [yoneda_embedding], intro f, exact F f x},
    { intro c' c'' f, esimp [yoneda_embedding], apply eq_of_homotopy, intro f',
      refine _ ⬝ ap (λy, to_fun_hom F y x) !(@id_left _ C)⁻¹,
      exact ap10 !(@respect_comp Cᵒᵖ cset)⁻¹ x}
  end

  definition yoneda_lemma_equiv [constructor] {C : Precategory} (c : C)
    (F : Cᵒᵖ ⇒ cset) : hom (ɏ c) F ≃ lift (F c) :=
  begin
    fapply equiv.MK,
    { intro η, exact up (η c id)},
    { intro x, induction x with x, exact yoneda_lemma_hom c F x},
    { exact abstract begin intro x, induction x with x, esimp, apply ap up,
      exact ap10 !respect_id x end end},
    { exact abstract begin intro η, esimp, apply nat_trans_eq,
      intro c', esimp, apply eq_of_homotopy,
      intro f, esimp [yoneda_embedding] at f,
      transitivity (F f ∘ η c) id, reflexivity,
      rewrite naturality, esimp [yoneda_embedding], rewrite [id_left], apply ap _ !id_left end end},
  end

  definition yoneda_lemma {C : Precategory} (c : C) (F : Cᵒᵖ ⇒ cset) :
    homset (ɏ c) F ≅ lift_functor (F c) :=
  begin
    apply iso_of_equiv, esimp, apply yoneda_lemma_equiv,
  end

  theorem yoneda_lemma_natural_ob {C : Precategory} (F : Cᵒᵖ ⇒ cset) {c c' : C} (f : c' ⟶ c)
    (η : ɏ c ⟹ F) :
     to_fun_hom (lift_functor ∘f F) f (to_hom (yoneda_lemma c F) η) =
     to_hom (yoneda_lemma c' F) (η ∘n to_fun_hom ɏ f) :=
  begin
    esimp [yoneda_lemma,yoneda_embedding], apply ap up,
    transitivity (F f ∘ η c) id, reflexivity,
    rewrite naturality,
    esimp [yoneda_embedding],
    apply ap (η c'),
    esimp [yoneda_embedding, Opposite],
    rewrite [+id_left,+id_right],
  end

  -- TODO: Investigate what is the bottleneck to type check the next theorem

  -- attribute yoneda_lemma lift_functor Precategory_hset precategory_hset homset
  --   yoneda_embedding nat_trans.compose functor_nat_trans_compose [reducible]
  -- attribute tlift functor.compose [reducible]
  theorem yoneda_lemma_natural_functor.{u v} {C : Precategory.{u v}} (c : C) (F F' : Cᵒᵖ ⇒ cset)
    (θ : F ⟹ F') (η : to_fun_ob ɏ c ⟹ F) :
     (lift_functor.{v u} ∘fn θ) c (to_hom (yoneda_lemma c F) η) =
     proof to_hom (yoneda_lemma c F') (θ ∘n η) qed :=
  by reflexivity

  -- theorem xx.{u v} {C : Precategory.{u v}} (c : C) (F F' : Cᵒᵖ ⇒ set)
  --   (θ : F ⟹ F') (η : to_fun_ob ɏ c ⟹ F) :
  --    proof _ qed =
  --    to_hom (yoneda_lemma c F') (θ ∘n η) :=
  -- by reflexivity

  -- theorem yy.{u v} {C : Precategory.{u v}} (c : C) (F F' : Cᵒᵖ ⇒ set)
  --   (θ : F ⟹ F') (η : to_fun_ob ɏ c ⟹ F) :
  --    (lift_functor.{v u} ∘fn θ) c (to_hom (yoneda_lemma c F) η) =
  --    proof _ qed :=
  -- by reflexivity

  definition fully_faithful_yoneda_embedding [instance] (C : Precategory) :
    fully_faithful (ɏ : C ⇒ cset ^c Cᵒᵖ) :=
  begin
    intro c c',
    fapply is_equiv_of_equiv_of_homotopy,
    { symmetry, transitivity _, apply @equiv_of_iso (homset _ _),
      rexact yoneda_lemma c (ɏ c'), esimp [yoneda_embedding], exact !equiv_lift⁻¹ᵉ},
    { intro f, apply nat_trans_eq, intro c, apply eq_of_homotopy, intro f',
      esimp [equiv.symm,equiv.trans],
      esimp [yoneda_lemma,yoneda_embedding,Opposite],
      rewrite [id_left,id_right]}
  end

  definition is_embedding_yoneda_embedding (C : Category) :
    is_embedding (ɏ : C → Cᵒᵖ ⇒ cset) :=
  begin
    intro c c', fapply is_equiv_of_equiv_of_homotopy,
    { exact !eq_equiv_iso ⬝e !iso_equiv_F_iso_F ⬝e !eq_equiv_iso⁻¹ᵉ},
    { intro p, induction p, esimp [equiv.trans, equiv.symm],
      esimp [to_fun_iso],
      rewrite -eq_of_iso_refl,
      apply ap eq_of_iso, apply iso_eq, esimp,
      apply nat_trans_eq, intro c',
      apply eq_of_homotopy, esimp [yoneda_embedding], intro f,
      rewrite [category.category.id_left], apply id_right}
  end

  definition is_representable {C : Precategory} (F : Cᵒᵖ ⇒ cset) := Σ(c : C), ɏ c ≅ F

  set_option unifier.max_steps 25000 -- TODO: fix this
  definition is_hprop_representable {C : Category} (F : Cᵒᵖ ⇒ cset)
    : is_hprop (is_representable F) :=
  begin
    fapply is_trunc_equiv_closed,
    { transitivity (Σc, ɏ c = F),
      { exact fiber.sigma_char ɏ F},
      { apply sigma.sigma_equiv_sigma_id, intro c, apply eq_equiv_iso}},
    { apply function.is_hprop_fiber_of_is_embedding, apply is_embedding_yoneda_embedding}
  end

end yoneda
