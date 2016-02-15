/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Cones of a diagram in a category
-/

import ..nat_trans ..category

open functor nat_trans eq equiv is_trunc is_equiv iso sigma sigma.ops pi

namespace category

  structure cone_obj {I C : Precategory} (F : I ⇒ C) :=
  (c : C)
  (η : constant_functor I c ⟹ F)

  variables {I C D : Precategory} {F : I ⇒ C} {x y z : cone_obj F} {i : I}

  definition cone_to_obj [unfold 4] := @cone_obj.c
  definition cone_to_nat [unfold 4] (c : cone_obj F) : constant_functor I (cone_to_obj c) ⟹ F :=
  cone_obj.η c

  local attribute cone_to_obj [coercion]

  structure cone_hom (x y : cone_obj F) :=
  (f : x ⟶ y)
  (p : Πi, cone_to_nat y i ∘ f = cone_to_nat x i)

  definition cone_to_hom [unfold 6] := @cone_hom.f
  definition cone_to_eq [unfold 6] (f : cone_hom x y) (i : I)
    : cone_to_nat y i ∘ (cone_to_hom f) = cone_to_nat x i :=
  cone_hom.p f i

  local attribute cone_to_hom [coercion]

  definition cone_id [constructor] (x : cone_obj F) : cone_hom x x :=
  cone_hom.mk id
              (λi, !id_right)

  definition cone_comp [constructor] (g : cone_hom y z) (f : cone_hom x y) : cone_hom x z :=
  cone_hom.mk (cone_to_hom g ∘ cone_to_hom f)
              abstract λi, by rewrite [assoc, +cone_to_eq] end

  definition cone_obj_eq (p : cone_to_obj x = cone_to_obj y)
    (q : Πi, cone_to_nat x i = cone_to_nat y i ∘ hom_of_eq p) : x = y :=
  begin
    induction x, induction y, esimp at *, induction p, apply ap (cone_obj.mk c),
    apply nat_trans_eq, intro i, exact q i ⬝ !id_right
  end

  theorem c_cone_obj_eq (p : cone_to_obj x = cone_to_obj y)
    (q : Πi, cone_to_nat x i = cone_to_nat y i ∘ hom_of_eq p) : ap cone_to_obj (cone_obj_eq p q) = p :=
  begin
    induction x, induction y, esimp at *, induction p,
    esimp [cone_obj_eq], rewrite [-ap_compose,↑function.compose,ap_constant]
  end

  theorem cone_hom_eq {f f' : cone_hom x y} (q : cone_to_hom f = cone_to_hom f') : f = f' :=
  begin
    induction f, induction f', esimp at *, induction q, apply ap (cone_hom.mk f),
    apply @is_prop.elim, apply pi.is_trunc_pi, intro x, apply is_trunc_eq, -- type class fails
  end

  variable (F)

  definition precategory_cone [instance] [constructor] : precategory (cone_obj F) :=
  @precategory.mk _ cone_hom
                 abstract begin
                   intro x y,
                   assert H : cone_hom x y ≃ Σ(f : x ⟶ y), Πi, cone_to_nat y i ∘ f = cone_to_nat x i,
                   { fapply equiv.MK,
                     { intro f, induction f, constructor, assumption},
                     { intro v, induction v, constructor, assumption},
                     { intro v, induction v, reflexivity},
                     { intro f, induction f, reflexivity}},
                   apply is_trunc.is_trunc_equiv_closed_rev, exact H,
                   fapply sigma.is_trunc_sigma, intros,
                   apply is_trunc_succ, apply pi.is_trunc_pi, intros, esimp,
                   /-exact _,-/ -- type class inference fails here
                   apply is_trunc_eq,
                 end end
                 (λx y z, cone_comp)
                 cone_id
                 abstract begin intros, apply cone_hom_eq, esimp, apply assoc    end end
                 abstract begin intros, apply cone_hom_eq, esimp, apply id_left  end end
                 abstract begin intros, apply cone_hom_eq, esimp, apply id_right end end

  definition cone [constructor] : Precategory :=
  precategory.Mk (precategory_cone F)

  variable {F}
  definition cone_iso_pr1 [constructor] (h : x ≅ y) : cone_to_obj x ≅ cone_to_obj y :=
  iso.MK
    (cone_to_hom (to_hom h))
    (cone_to_hom (to_inv h))
    (ap cone_to_hom (to_left_inverse h))
    (ap cone_to_hom (to_right_inverse h))


  definition cone_iso.mk [constructor] (f : cone_to_obj x ≅ cone_to_obj y)
    (p : Πi, cone_to_nat y i ∘ to_hom f = cone_to_nat x i) : x ≅ y :=
  begin
    fapply iso.MK,
    { exact !cone_hom.mk p},
    { fapply cone_hom.mk,
      { exact to_inv f},
      { intro i, apply comp_inverse_eq_of_eq_comp, exact (p i)⁻¹}},
    { apply cone_hom_eq, esimp, apply left_inverse},
    { apply cone_hom_eq, esimp, apply right_inverse},
  end

  variables (x y)
  definition cone_iso_equiv [constructor] : (x ≅ y) ≃ Σ(f : cone_to_obj x ≅ cone_to_obj y),
                                          Πi, cone_to_nat y i ∘ to_hom f = cone_to_nat x i :=
  begin
    fapply equiv.MK,
    { intro h, exact ⟨cone_iso_pr1 h, cone_to_eq (to_hom h)⟩},
    { intro v, exact cone_iso.mk v.1 v.2},
    { intro v, induction v with f p, fapply sigma_eq: esimp,
      { apply iso_eq, reflexivity},
      { apply is_prop.elimo, apply is_trunc_pi, intro i, apply is_prop_hom_eq}},
    { intro h, esimp, apply iso_eq, apply cone_hom_eq, reflexivity},
  end

  definition cone_eq_equiv : (x = y) ≃ Σ(f : cone_to_obj x = cone_to_obj y),
                                          Πi, cone_to_nat y i ∘ hom_of_eq f = cone_to_nat x i :=
  begin
    fapply equiv.MK,
    { intro r, fapply sigma.mk, exact ap cone_to_obj r, induction r, intro i, apply id_right},
    { intro v, induction v with p q, induction x with c η, induction y with c' η', esimp at *,
      apply cone_obj_eq p, esimp, intro i, exact (q i)⁻¹},
    { intro v, induction v with p q, induction x with c η, induction y with c' η', esimp at *,
      induction p, esimp, fapply sigma_eq: esimp,
      { apply c_cone_obj_eq},
      { apply is_prop.elimo, apply is_trunc_pi, intro i, apply is_prop_hom_eq}},
    { intro r, induction r, esimp, induction x, esimp, apply ap02, apply is_prop.elim},
  end

  section is_univalent

    definition is_univalent_cone {I : Precategory} {C : Category} (F : I ⇒ C)
      : is_univalent (cone F) :=
    begin
      intro x y,
      fapply is_equiv_of_equiv_of_homotopy,
      { exact calc
(x = y) ≃ (Σ(f : cone_to_obj x = cone_to_obj y), Πi, cone_to_nat y i ∘ hom_of_eq f = cone_to_nat x i)
                  : cone_eq_equiv
    ... ≃ (Σ(f : cone_to_obj x ≅ cone_to_obj y), Πi, cone_to_nat y i ∘ to_hom f = cone_to_nat x i)
                  : sigma_equiv_sigma !eq_equiv_iso (λa, !equiv.refl)
    ... ≃ (x ≅ y) : cone_iso_equiv },
      { intro p, induction p, esimp [equiv.trans,equiv.symm], esimp [sigma_functor],
        apply iso_eq, reflexivity}
    end

    definition category_cone [instance] [constructor] {I : Precategory} {C : Category} (F : I ⇒ C)
      : category (cone_obj F) :=
    category.mk _ (is_univalent_cone F)

    definition Category_cone [constructor] {I : Precategory} {C : Category} (F : I ⇒ C)
      : Category :=
    Category.mk _ (category_cone F)

  end is_univalent

  definition cone_obj_compose [constructor] (G : C ⇒ D) (x : cone_obj F) : cone_obj (G ∘f F) :=
  begin
  fapply cone_obj.mk,
  { exact G x},
  { fapply change_natural_map,
    { refine ((G ∘fn cone_to_nat x) ∘n _), apply nat_trans_of_eq, fapply functor_eq: esimp,
      intro i j k, esimp, rewrite [id_leftright,respect_id]},
    { intro i, esimp, exact G (cone_to_nat x i)},
    { intro i, esimp, rewrite [ap010_functor_eq, ▸*, id_right]}}
  end

end category
