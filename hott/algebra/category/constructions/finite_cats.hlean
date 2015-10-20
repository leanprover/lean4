/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Some finite categories which are neither discrete nor indiscrete
-/

import ..functor.functor types.sum

open bool unit is_trunc sum eq functor equiv

namespace category

  variables {A : Type} (R : A → A → Type) (H : Π⦃a b c⦄, R a b → R b c → empty)
    [HR : Πa b, is_hset (R a b)] [HA : is_trunc 1 A]

  include H HR HA

  -- we call a category sparse if you cannot compose two morphism, except the ones which come from equality
  definition sparse_category' [constructor] : precategory A :=
  precategory.mk
    (λa b, R a b ⊎ a = b)
    begin
      intros a b c g f, induction g with rg pg: induction f with rf pf,
      { exfalso, exact H rf rg},
      { exact inl (pf⁻¹ ▸ rg)},
      { exact inl (pg ▸ rf)},
      { exact inr (pf ⬝ pg)},
    end
    (λa, inr idp)
    abstract begin
      intros a b c d h g f, induction h with rh ph: induction g with rg pg: induction f with rf pf:
      esimp: try induction pf; try induction pg; try induction ph: esimp;
      try (exfalso; apply H;assumption;assumption)
    end end
    abstract by intros a b f; induction f with rf pf: reflexivity end
    abstract by intros a b f; (induction f with rf pf: esimp); rewrite idp_con end

  definition sparse_category [constructor] : Precategory :=
  precategory.Mk (sparse_category' R @H)

  definition sparse_category_functor [constructor] (C : Precategory) (f : A → C)
    (g : Π{a b} (r : R a b), f a ⟶ f b) : sparse_category R H ⇒ C :=
  functor.mk f
             (λa b, sum.rec g (eq.rec id))
             (λa, idp)
             abstract begin
               intro a b c g f, induction g with rg pg: induction f with rf pf: esimp:
               try induction pg: try induction pf: esimp,
                 exfalso, exact H rf rg,
                 exact !id_right⁻¹,
                 exact !id_left⁻¹,
                 exact !id_id⁻¹
             end end

  omit H HR HA

  section equalizer
  inductive equalizer_category_hom : bool → bool → Type :=
  | f1 : equalizer_category_hom ff tt
  | f2 : equalizer_category_hom ff tt

  open equalizer_category_hom
  theorem is_hset_equalizer_category_hom (b₁ b₂ : bool) : is_hset (equalizer_category_hom b₁ b₂) :=
  begin
    assert H : Πb b', equalizer_category_hom b b' ≃ bool.rec (bool.rec empty bool) (λb, empty) b b',
    { intro b b', fapply equiv.MK,
      { intro x, induction x, exact ff, exact tt},
      { intro v, induction b: induction b': induction v, exact f1, exact f2},
      { intro v, induction b: induction b': induction v: reflexivity},
      { intro x, induction x: reflexivity}},
    apply is_trunc_equiv_closed_rev, apply H,
    induction b₁: induction b₂: exact _
  end

  local attribute is_hset_equalizer_category_hom [instance]
  definition equalizer_category [constructor] : Precategory :=
  sparse_category
    equalizer_category_hom
    begin intro a b c g f; cases g: cases f end

  definition equalizer_category_functor [constructor] (C : Precategory) {x y : C} (f g : x ⟶ y)
    : equalizer_category ⇒ C :=
  sparse_category_functor _ _ C
    (bool.rec x y)
    begin intro a b h; induction h, exact f, exact g end
  end equalizer

  section pullback
  inductive pullback_category_ob : Type :=
  | TR : pullback_category_ob
  | BL : pullback_category_ob
  | BR : pullback_category_ob

  theorem pullback_category_ob_decidable_equality : decidable_eq pullback_category_ob :=
  begin
    intro x y; induction x: induction y:
      try exact decidable.inl idp:
      apply decidable.inr; contradiction
  end

  open pullback_category_ob
  inductive pullback_category_hom : pullback_category_ob → pullback_category_ob → Type :=
  | f1 : pullback_category_hom TR BR
  | f2 : pullback_category_hom BL BR

  open pullback_category_hom
  theorem is_hset_pullback_category_hom (b₁ b₂ : pullback_category_ob)
    : is_hset (pullback_category_hom b₁ b₂) :=
  begin
    assert H : Πb b', pullback_category_hom b b' ≃
      pullback_category_ob.rec (λb, empty) (λb, empty)
                              (pullback_category_ob.rec unit unit empty) b' b,
    { intro b b', fapply equiv.MK,
      { intro x, induction x: exact star},
      { intro v, induction b: induction b': induction v, exact f1, exact f2},
      { intro v, induction b: induction b': induction v: reflexivity},
      { intro x, induction x: reflexivity}},
    apply is_trunc_equiv_closed_rev, apply H,
    induction b₁: induction b₂: exact _
  end

  local attribute is_hset_pullback_category_hom pullback_category_ob_decidable_equality [instance]
  definition pullback_category [constructor] : Precategory :=
  sparse_category
    pullback_category_hom
    begin intro a b c g f; cases g: cases f end

  definition pullback_category_functor [constructor] (C : Precategory) {x y z : C}
    (f : x ⟶ z) (g : y ⟶ z) : pullback_category ⇒ C :=
  sparse_category_functor _ _ C
    (pullback_category_ob.rec x y z)
    begin intro a b h; induction h, exact f, exact g end
  end pullback

end category
