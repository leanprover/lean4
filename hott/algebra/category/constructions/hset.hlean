/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Category of hsets
-/

import ..category types.equiv types.lift ..colimits hit.set_quotient

open eq category equiv iso is_equiv is_trunc function sigma set_quotient trunc

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

  abbreviation set [constructor] := Precategory_hset

  namespace set
    local attribute is_equiv_subtype_eq [instance]
    definition iso_of_equiv [constructor] {A B : set} (f : A ≃ B) : A ≅ B :=
    iso.MK (to_fun f)
           (to_inv f)
           (eq_of_homotopy (left_inv (to_fun f)))
           (eq_of_homotopy (right_inv (to_fun f)))

    definition equiv_of_iso [constructor] {A B : set} (f : A ≅ B) : A ≃ B :=
    begin
      apply equiv.MK (to_hom f) (iso.to_inv f),
        exact ap10 (to_right_inverse f),
        exact ap10 (to_left_inverse f)
    end

    definition is_equiv_iso_of_equiv [constructor] (A B : set)
      : is_equiv (@iso_of_equiv A B) :=
    adjointify _ (λf, equiv_of_iso f)
                 (λf, proof iso_eq idp qed)
                 (λf, equiv_eq idp)

    local attribute is_equiv_iso_of_equiv [instance]

    definition iso_of_eq_eq_compose (A B : hset) : @iso_of_eq _ _ A B =
      @iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
      @ap _ _ (to_fun (trunctype.sigma_char 0)) A B :=
    eq_of_homotopy (λp, eq.rec_on p idp)

    definition equiv_equiv_iso (A B : set) : (A ≃ B) ≃ (A ≅ B) :=
    equiv.MK (λf, iso_of_equiv f)
             (λf, proof equiv.MK (to_hom f)
                           (iso.to_inv f)
                           (ap10 (to_right_inverse f))
                           (ap10 (to_left_inverse  f)) qed)
             (λf, proof iso_eq idp qed)
             (λf, proof equiv_eq idp qed)

    definition equiv_eq_iso (A B : set) : (A ≃ B) = (A ≅ B) :=
    ua !equiv_equiv_iso

    definition is_univalent_hset (A B : set) : is_equiv (iso_of_eq : A = B → A ≅ B) :=
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

  definition category_hset [instance] [constructor] [reducible] : category hset :=
  category.mk precategory_hset set.is_univalent_hset

  definition Category_hset [reducible] [constructor] : Category :=
  Category.mk hset category_hset

  abbreviation cset [constructor] := Category_hset

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
    { with_options [elaborator.ignore_instances true] -- TODO: fix
      ( refine is_trunc_sigma _ _;
        ( apply is_trunc_pi);
        ( intro s;
          refine is_trunc_pi _ _; intro i;
          refine is_trunc_pi _ _; intro j;
          refine is_trunc_pi _ _; intro f;
          apply is_trunc_eq))}},
  { fapply nat_trans.mk,
    { intro i x, esimp at x, exact x.1 i},
    { intro i j f, esimp, apply eq_of_homotopy, intro x, esimp at x, induction x with s p,
      esimp, apply p}}
  end

  definition is_complete_set.{u v w} [instance] : is_complete.{(max u v w)+1 (max u v w) v w} set :=
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
        { with_options [elaborator.ignore_instances true] -- TODO: fix
          ( refine is_hprop.elimo _ _ _;
            refine is_trunc_pi _ _; intro i;
            refine is_trunc_pi _ _; intro j;
            refine is_trunc_pi _ _; intro f;
            apply is_trunc_eq)}}}
  end

  definition is_cocomplete_set_cone_rel.{u v w} [unfold 3 4]
    (I : Precategory.{v w}) (F : I ⇒ set.{max u v w}ᵒᵖ) : (Σ(i : I), trunctype.carrier (F i)) →
    (Σ(i : I), trunctype.carrier (F i)) → hprop.{max u v w} :=
  begin
    intro v w, induction v with i x, induction w with j y,
      fapply trunctype.mk,
      { exact ∃(f : i ⟶ j), to_fun_hom F f y = x},
      { exact _}
  end

  definition is_cocomplete_set_cone.{u v w} [constructor]
    (I : Precategory.{v w}) (F : I ⇒ set.{max u v w}ᵒᵖ) : cone_obj F :=
  begin
  fapply cone_obj.mk,
  { fapply trunctype.mk,
    { apply set_quotient (is_cocomplete_set_cone_rel.{u v w} I F)},
    { apply is_hset_set_quotient}},
  { fapply nat_trans.mk,
    { intro i x, esimp, apply class_of, exact ⟨i, x⟩},
    { intro i j f, esimp, apply eq_of_homotopy, intro y, apply eq_of_rel, esimp,
      exact exists.intro f idp}}
  end

  -- TODO: change this after induction tactic for trunc/set_quotient is implemented
  definition is_cocomplete_set.{u v w} [instance]
    : is_cocomplete.{(max u v w)+1 (max u v w) v w} set :=
  begin
    intro I F, fapply has_terminal_object.mk,
    { exact is_cocomplete_set_cone.{u v w} I F},
    { intro c, esimp at *, induction c with X η, induction η with η p, esimp at *,
      fapply is_contr.mk,
      { fapply cone_hom.mk,
        { refine set_quotient.elim _ _,
          { intro v, induction v with i x, exact η i x},
          { intro v w r, induction v with i x, induction w with j y, esimp at *,
            refine trunc.elim_on r _, clear r,
            intro u, induction u with f q,
            exact ap (η i) q⁻¹ ⬝ ap10 (p f) y}},
        { intro i, reflexivity}},
      { esimp, intro h, induction h with f q, apply cone_hom_eq, esimp at *,
        apply eq_of_homotopy, refine set_quotient.rec _ _,
        { intro v, induction v with i x, esimp, exact (ap10 (q i) x)⁻¹},
        { intro v w r, apply is_hprop.elimo}}},
  end



end category
