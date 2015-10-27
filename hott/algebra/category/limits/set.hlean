/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

The category of sets is complete and cocomplete
-/

import .colimits ..constructions.set hit.set_quotient

open eq functor is_trunc sigma pi sigma.ops trunc set_quotient

namespace category
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
