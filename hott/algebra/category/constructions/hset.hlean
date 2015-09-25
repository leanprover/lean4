/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Category of hsets
-/

import ..category types.equiv ..functor types.lift ..limits

open eq category equiv iso is_equiv is_trunc function sigma

namespace category

  definition precategory_hset.{u} [reducible] [constructor] : precategory hset.{u} :=
  precategory.mk (λx y : hset, x → y)
                 (λx y z g f a, g (f a))
                 (λx a, a)
                 (λx y z w h g f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))

  definition Precategory_hset [reducible] [constructor] : Precategory :=
  Precategory.mk hset precategory_hset

  namespace set
    local attribute is_equiv_subtype_eq [instance]
    definition iso_of_equiv [constructor] {A B : Precategory_hset} (f : A ≃ B) : A ≅ B :=
    iso.MK (to_fun f)
           (to_inv f)
           (eq_of_homotopy (left_inv (to_fun f)))
           (eq_of_homotopy (right_inv (to_fun f)))

    definition equiv_of_iso [constructor] {A B : Precategory_hset} (f : A ≅ B) : A ≃ B :=
    begin
      apply equiv.MK (to_hom f) (iso.to_inv f),
        exact ap10 (to_right_inverse f),
        exact ap10 (to_left_inverse f)
    end

    definition is_equiv_iso_of_equiv [constructor] (A B : Precategory_hset)
      : is_equiv (@iso_of_equiv A B) :=
    adjointify _ (λf, equiv_of_iso f)
                 (λf, proof iso_eq idp qed)
                 (λf, equiv_eq idp)

    local attribute is_equiv_iso_of_equiv [instance]

    definition iso_of_eq_eq_compose (A B : hset) : @iso_of_eq _ _ A B =
      @iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
      @ap _ _ (to_fun (trunctype.sigma_char 0)) A B :=
    eq_of_homotopy (λp, eq.rec_on p idp)

    definition equiv_equiv_iso (A B : Precategory_hset) : (A ≃ B) ≃ (A ≅ B) :=
    equiv.MK (λf, iso_of_equiv f)
             (λf, proof equiv.MK (to_hom f)
                           (iso.to_inv f)
                           (ap10 (to_right_inverse f))
                           (ap10 (to_left_inverse  f)) qed)
             (λf, proof iso_eq idp qed)
             (λf, proof equiv_eq idp qed)

    definition equiv_eq_iso (A B : Precategory_hset) : (A ≃ B) = (A ≅ B) :=
    ua !equiv_equiv_iso

    definition is_univalent_hset (A B : Precategory_hset) : is_equiv (iso_of_eq : A = B → A ≅ B) :=
    assert H₁ : is_equiv (@iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
                  @ap _ _ (to_fun (trunctype.sigma_char 0)) A B), from
      @is_equiv_compose _ _ _ _ _
      (@is_equiv_compose _ _ _ _ _
         (@is_equiv_compose _ _ _ _ _
           _
           (@is_equiv_subtype_eq_inv _ _ _ _ _))
         !univalence)
       !is_equiv_iso_of_equiv,
    let H₂ := (iso_of_eq_eq_compose A B)⁻¹ in
    begin
      rewrite H₂ at H₁,
      assumption
    end
  end set

  definition category_hset [instance] [constructor] : category hset :=
  category.mk precategory_hset set.is_univalent_hset

  definition Category_hset [reducible] [constructor] : Category :=
  Category.mk hset category_hset

  abbreviation set [constructor] := Category_hset

  open functor lift
  definition lift_functor.{u v} [constructor] : set.{u} ⇒ set.{max u v} :=
  functor.mk tlift
             (λa b, lift_functor)
             (λa, eq_of_homotopy (λx, by induction x; reflexivity))
             (λa b c g f, eq_of_homotopy (λx, by induction x; reflexivity))

  open pi sigma.ops
  local attribute Category.to.precategory [unfold 1]
  local attribute category.to_precategory [unfold 2]

  definition is_complete_set_cone.{u v w} [constructor]
    (I : Precategory.{v w}) (F : I ⇒ set.{max u v w}) : cone_obj F :=
  begin
  fapply cone_obj.mk,
  { fapply trunctype.mk,
    { exact Σ(s : Π(i : I), trunctype.carrier (F i)),
        Π{i j : I} (f : i ⟶ j), F f (s i) = (s j)},
    { exact abstract begin apply is_trunc_sigma, intro s,
      apply is_trunc_pi, intro i,
      apply is_trunc_pi, intro j,
      apply is_trunc_pi, intro f,
      apply is_trunc_eq end end}},
  { fapply nat_trans.mk,
    { intro i x, esimp at x, exact x.1 i},
    { intro i j f, esimp, apply eq_of_homotopy, intro x, esimp at x, induction x with s p,
      esimp, apply p}}
  end

  definition is_complete_set.{u v w} : is_complete.{(max u v w)+1 (max u v w) v w} set :=
  begin
    intro I F, fapply has_terminal_object.mk,
    { exact is_complete_set_cone.{u v w} I F},
    { intro c, esimp at *, induction c with X η, induction η with η p, esimp at *,
      fapply is_contr.mk,
      { fapply cone_hom.mk,
        { intro x, esimp at *, fapply sigma.mk,
          { intro i, exact η i x},
          { intro i j f, exact ap10 (p f) x}},
        { intro i, reflexivity}},
      { esimp, intro h, induction h with f q, apply cone_hom_eq, esimp at *,
        apply eq_of_homotopy, intro x, fapply sigma_eq: esimp,
        { apply eq_of_homotopy, intro i, exact (ap10 (q i) x)⁻¹},
        { apply is_hprop.elimo,
          apply is_trunc_pi, intro i,
          apply is_trunc_pi, intro j,
          apply is_trunc_pi, intro f,
          apply is_trunc_eq}}}
  end
end category
