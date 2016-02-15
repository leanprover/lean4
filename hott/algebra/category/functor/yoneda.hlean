/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Yoneda embedding and Yoneda lemma
-/

import .examples .attributes

open category eq functor prod.ops is_trunc iso is_equiv equiv category.set nat_trans lift

namespace yoneda

  /-
    These attributes make sure that the fields of the category "set" reduce to the right things
    However, we don't want to have them globally, because that will unfold the composition g ∘ f
    in a Category to category.category.comp g f
  -/
  local attribute category.to_precategory [constructor]

  -- should this be defined as "yoneda_embedding Cᵒᵖ"?
  definition contravariant_yoneda_embedding [constructor] [reducible]
    (C : Precategory) : Cᵒᵖ ⇒ cset ^c C :=
  functor_curry !hom_functor

  /-
    we use (change_fun) to make sure that (to_fun_ob (yoneda_embedding C) c) will reduce to
    (hom_functor_left c) instead of (functor_curry_rev_ob (hom_functor C) c)
  -/
  definition yoneda_embedding [constructor] (C : Precategory) : C ⇒ cset ^c Cᵒᵖ :=
--(functor_curry_rev !hom_functor)
  change_fun
    (functor_curry_rev !hom_functor)
    hom_functor_left
    nat_trans_hom_functor_left
    idp
    idpo

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
    (F : Cᵒᵖ ⇒ cset) : hom (ɏ c) F ≃ lift (trunctype.carrier (to_fun_ob F c)) :=
  begin
    fapply equiv.MK,
    { intro η, exact up (η c id)},
    { intro x, induction x with x, exact yoneda_lemma_hom c F x},
    { exact abstract begin intro x, induction x with x, esimp, apply ap up,
      exact ap10 !respect_id x end end},
    { exact abstract begin intro η, esimp, apply nat_trans_eq,
      intro c', esimp, apply eq_of_homotopy,
      intro f,
      transitivity (F f ∘ η c) id, reflexivity,
      rewrite naturality, esimp [yoneda_embedding], rewrite [id_left], apply ap _ !id_left end end},
  end

  definition yoneda_lemma {C : Precategory} (c : C) (F : Cᵒᵖ ⇒ cset) :
    homset (ɏ c) F ≅ functor_lift (F c) :=
  begin
    apply iso_of_equiv, esimp, apply yoneda_lemma_equiv,
  end

  theorem yoneda_lemma_natural_ob {C : Precategory} (F : Cᵒᵖ ⇒ cset) {c c' : C} (f : c' ⟶ c)
    (η : ɏ c ⟹ F) :
     to_fun_hom (functor_lift ∘f F) f (to_hom (yoneda_lemma c F) η) =
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

  -- attribute yoneda_lemma functor_lift Precategory_hset precategory_hset homset
  --   yoneda_embedding nat_trans.compose functor_nat_trans_compose [reducible]
  -- attribute tlift functor.compose [reducible]
  theorem yoneda_lemma_natural_functor.{u v} {C : Precategory.{u v}} (c : C) (F F' : Cᵒᵖ ⇒ cset)
    (θ : F ⟹ F') (η : to_fun_ob ɏ c ⟹ F) :
     (functor_lift.{v u} ∘fn θ) c (to_hom (yoneda_lemma c F) η) =
     proof to_hom (yoneda_lemma c F') (θ ∘n η) qed :=
  by reflexivity

  -- theorem xx.{u v} {C : Precategory.{u v}} (c : C) (F F' : Cᵒᵖ ⇒ set)
  --   (θ : F ⟹ F') (η : to_fun_ob ɏ c ⟹ F) :
  --    proof _ qed =
  --    to_hom (yoneda_lemma c F') (θ ∘n η) :=
  -- by reflexivity

  -- theorem yy.{u v} {C : Precategory.{u v}} (c : C) (F F' : Cᵒᵖ ⇒ set)
  --   (θ : F ⟹ F') (η : to_fun_ob ɏ c ⟹ F) :
  --    (functor_lift.{v u} ∘fn θ) c (to_hom (yoneda_lemma c F) η) =
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
    { intro p, induction p, esimp [equiv.trans, equiv.symm, to_fun_iso], -- to_fun_iso not unfolded
      esimp [to_fun_iso],
      rewrite -eq_of_iso_refl,
      apply ap eq_of_iso, apply iso_eq, esimp,
      apply nat_trans_eq, intro c',
      apply eq_of_homotopy, intro f,
      rewrite [▸*, category.category.id_left], apply id_right}
  end

  definition is_representable {C : Precategory} (F : Cᵒᵖ ⇒ cset) := Σ(c : C), ɏ c ≅ F

  section
    set_option apply.class_instance false
    definition is_prop_representable {C : Category} (F : Cᵒᵖ ⇒ cset)
      : is_prop (is_representable F) :=
    begin
      fapply is_trunc_equiv_closed,
      { exact proof fiber.sigma_char ɏ F qed ⬝e sigma.sigma_equiv_sigma_id (λc, !eq_equiv_iso)},
      { apply function.is_prop_fiber_of_is_embedding, apply is_embedding_yoneda_embedding}
    end
  end



end yoneda
