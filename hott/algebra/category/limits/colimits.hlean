/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Colimits in a category
-/

import .limits ..constructions.opposite

open is_trunc functor nat_trans eq

-- we define colimits to be the dual of a limit

namespace category

  variables {ob : Type} [C : precategory ob] {c c' : ob} (D I : Precategory)
  include C

  definition is_initial [reducible] (c : ob) := @is_terminal _ (opposite C) c

  definition is_contr_of_is_initial (c d : ob) [H : is_initial d]
    : is_contr (d ⟶ c) :=
  H c

  local attribute is_contr_of_is_initial [instance]

  definition initial_morphism (c c' : ob) [H : is_initial c'] : c' ⟶ c :=
  !center

  definition hom_initial_eq [H : is_initial c'] (f f' : c' ⟶ c) : f = f' :=
  !is_hprop.elim

  definition eq_initial_morphism [H : is_initial c'] (f : c' ⟶ c) : f = initial_morphism c c' :=
  !is_hprop.elim

  definition initial_iso_initial {c c' : ob} (H : is_initial c) (K : is_initial c') : c ≅ c' :=
  iso_of_opposite_iso (@terminal_iso_terminal _ (opposite C) _ _ H K)

  theorem is_hprop_is_initial [instance] : is_hprop (is_initial c) := _

  omit C

  definition has_initial_object [reducible] : Type := has_terminal_object Dᵒᵖ

  definition initial_object [unfold 2] [reducible] [H : has_initial_object D] : D :=
  has_terminal_object.d Dᵒᵖ

  definition has_initial_object.is_initial [H : has_initial_object D]
    : is_initial (initial_object D) :=
  @has_terminal_object.is_terminal (Opposite D) H

  variable {D}
  definition initial_object_iso_initial_object (H₁ H₂ : has_initial_object D)
    : @initial_object D H₁ ≅ @initial_object D H₂ :=
  initial_iso_initial (@has_initial_object.is_initial D H₁) (@has_initial_object.is_initial D H₂)

  set_option pp.coercions true
  theorem is_hprop_has_initial_object [instance] (D : Category)
    : is_hprop (has_initial_object D) :=
  is_hprop_has_terminal_object (Category_opposite D)

  variable (D)
  abbreviation has_colimits_of_shape := has_limits_of_shape Dᵒᵖ Iᵒᵖ

  /-
    The next definitions states that a category is cocomplete with respect to diagrams
    in a certain universe. "is_cocomplete.{o₁ h₁ o₂ h₂}" means that D is cocomplete
    with respect to diagrams of type Precategory.{o₂ h₂}
  -/

  abbreviation is_cocomplete (D : Precategory) := is_complete Dᵒᵖ

  definition has_colimits_of_shape_of_is_cocomplete [instance] [H : is_cocomplete D]
    (I : Precategory) : has_colimits_of_shape D I := H Iᵒᵖ

  section
    open pi
    theorem is_hprop_has_colimits_of_shape [instance] (D : Category) (I : Precategory)
      : is_hprop (has_colimits_of_shape D I) :=
    is_hprop_has_limits_of_shape (Category_opposite D) _

    theorem is_hprop_is_cocomplete [instance] (D : Category) : is_hprop (is_cocomplete D) :=
    is_hprop_is_complete (Category_opposite D)
  end

  variables {D I} (F : I ⇒ D) [H : has_colimits_of_shape D I] {i j : I}
  include H

  abbreviation cocone := (cone Fᵒᵖᶠ)ᵒᵖ

  definition has_initial_object_cocone [H : has_colimits_of_shape D I]
    (F : I ⇒ D) : has_initial_object (cocone F) :=
  begin
    unfold [has_colimits_of_shape,has_limits_of_shape] at H,
    exact H Fᵒᵖᶠ
  end
  local attribute has_initial_object_cocone [instance]

  definition colimit_cocone : cocone F := limit_cone Fᵒᵖᶠ

  definition is_initial_colimit_cocone [instance] : is_initial (colimit_cocone F) :=
  is_terminal_limit_cone Fᵒᵖᶠ

  definition colimit_object : D :=
  limit_object Fᵒᵖᶠ

  definition colimit_nat_trans : constant_functor Iᵒᵖ (colimit_object F) ⟹ Fᵒᵖᶠ :=
  limit_nat_trans Fᵒᵖᶠ

  definition colimit_morphism (i : I) : F i ⟶ colimit_object F :=
  limit_morphism Fᵒᵖᶠ i

  variable {H}
  theorem colimit_commute {i j : I} (f : i ⟶ j)
    : colimit_morphism F j ∘ to_fun_hom F f = colimit_morphism F i :=
  by rexact limit_commute Fᵒᵖᶠ f

  variable [H]
  definition colimit_cone_obj [constructor] {d : D} {η : Πi, F i ⟶ d}
    (p : Π⦃j i : I⦄ (f : i ⟶ j), η j ∘ to_fun_hom F f = η i) : cone_obj Fᵒᵖᶠ :=
  limit_cone_obj Fᵒᵖᶠ proof p qed

  variable {H}
  definition colimit_hom {d : D} (η : Πi, F i ⟶ d)
    (p : Π⦃j i : I⦄ (f : i ⟶ j), η j ∘ to_fun_hom F f = η i) : colimit_object F ⟶ d :=
  hom_limit Fᵒᵖᶠ η proof p qed

  theorem colimit_hom_commute {d : D} (η : Πi, F i ⟶ d)
    (p : Π⦃j i : I⦄ (f : i ⟶ j), η j ∘ to_fun_hom F f = η i) (i : I)
    : colimit_hom F η p ∘ colimit_morphism F i = η i :=
  by rexact hom_limit_commute Fᵒᵖᶠ η proof p qed i

  definition colimit_cone_hom [constructor] {d : D} {η : Πi, F i ⟶ d}
    (p : Π⦃j i : I⦄ (f : i ⟶ j), η j ∘ to_fun_hom F f = η i) {h : colimit_object F ⟶ d}
    (q : Πi, h ∘ colimit_morphism F i = η i)
    : cone_hom (colimit_cone_obj F p) (colimit_cocone F) :=
  by rexact limit_cone_hom Fᵒᵖᶠ proof p qed proof q qed

  variable {F}
  theorem eq_colimit_hom {d : D} {η : Πi, F i ⟶ d}
    (p : Π⦃j i : I⦄ (f : i ⟶ j), η j ∘ to_fun_hom F f = η i) {h : colimit_object F ⟶ d}
    (q : Πi, h ∘ colimit_morphism F i = η i) : h = colimit_hom F η p :=
  by rexact @eq_hom_limit _ _ Fᵒᵖᶠ _ _ _ proof p qed _ proof q qed

  theorem colimit_cocone_unique {d : D} {η : Πi, F i ⟶ d}
    (p : Π⦃j i : I⦄ (f : i ⟶ j), η j ∘ to_fun_hom F f = η i)
    {h₁ : colimit_object F ⟶ d} (q₁ : Πi, h₁ ∘ colimit_morphism F i = η i)
    {h₂ : colimit_object F ⟶ d} (q₂ : Πi, h₂ ∘ colimit_morphism F i = η i) : h₁ = h₂ :=
  @limit_cone_unique _ _ Fᵒᵖᶠ _ _ _ proof p qed _ proof q₁ qed _ proof q₂ qed

  definition colimit_hom_colimit [reducible] {F G : I ⇒ D} (η : F ⟹ G)
    : colimit_object F ⟶ colimit_object G :=
  colimit_hom _ (λi, colimit_morphism G i ∘ η i)
              abstract by intro i j f; rewrite [-assoc,-naturality,assoc,colimit_commute] end

  omit H

  variable (F)
  definition colimit_object_iso_colimit_object [constructor] (H₁ H₂ : has_colimits_of_shape D I) :
    @(colimit_object F) H₁ ≅ @(colimit_object F) H₂ :=
  iso_of_opposite_iso (limit_object_iso_limit_object Fᵒᵖᶠ H₁ H₂)

  definition colimit_functor [constructor] (D I : Precategory) [H : has_colimits_of_shape D I]
    : D ^c I ⇒ D :=
  (limit_functor Dᵒᵖ Iᵒᵖ ∘f opposite_functor_opposite_left D I)ᵒᵖ'

  section bin_coproducts
  open bool prod.ops
  definition has_binary_coproducts [reducible] (D : Precategory) := has_colimits_of_shape D c2
  variables [K : has_binary_coproducts D] (d d' : D)
  include K

  definition coproduct_object : D :=
  colimit_object (c2_functor D d d')

  infixr `+l`:27 := coproduct_object
  local infixr + := coproduct_object

  definition inl : d ⟶ d + d' :=
  colimit_morphism (c2_functor D d d') ff

  definition inr : d' ⟶ d + d' :=
  colimit_morphism (c2_functor D d d') tt

  variables {d d'}
  definition coproduct_hom {x : D} (f : d ⟶ x) (g : d' ⟶ x) : d + d' ⟶ x :=
  colimit_hom (c2_functor D d d') (bool.rec f g)
    (by intro b₁ b₂ f; induction b₁: induction b₂: esimp at *; try contradiction: apply id_right)

  theorem coproduct_hom_inl {x : D} (f : d ⟶ x) (g : d' ⟶ x) : coproduct_hom f g ∘ !inl = f :=
  colimit_hom_commute (c2_functor D d d') (bool.rec f g) _ ff

  theorem coproduct_hom_inr {x : D} (f : d ⟶ x) (g : d' ⟶ x) : coproduct_hom f g ∘ !inr = g :=
  colimit_hom_commute (c2_functor D d d') (bool.rec f g) _ tt

  theorem eq_coproduct_hom {x : D} {f : d ⟶ x} {g : d' ⟶ x} {h : d + d' ⟶ x}
    (p : h ∘ !inl = f) (q : h ∘ !inr = g) : h = coproduct_hom f g :=
  eq_colimit_hom _ (bool.rec p q)

  theorem coproduct_cocone_unique {x : D} {f : d ⟶ x} {g : d' ⟶ x}
    {h₁ : d + d' ⟶ x} (p₁ : h₁ ∘ !inl = f) (q₁ : h₁ ∘ !inr = g)
    {h₂ : d + d' ⟶ x} (p₂ : h₂ ∘ !inl = f) (q₂ : h₂ ∘ !inr = g) : h₁ = h₂ :=
  eq_coproduct_hom p₁ q₁ ⬝ (eq_coproduct_hom p₂ q₂)⁻¹

  variable (D)
  -- TODO: define this in terms of colimit_functor and functor_two_left (in exponential_laws)
  definition coproduct_functor [constructor] : D ×c D ⇒ D :=
  functor.mk
    (λx, coproduct_object x.1 x.2)
    (λx y f, coproduct_hom (!inl ∘ f.1) (!inr ∘ f.2))
    abstract begin intro x, symmetry, apply eq_coproduct_hom: apply id_comp_eq_comp_id end end
    abstract begin intro x y z g f, symmetry, apply eq_coproduct_hom,
                   rewrite [-assoc,coproduct_hom_inl,assoc,coproduct_hom_inl,-assoc],
                   rewrite [-assoc,coproduct_hom_inr,assoc,coproduct_hom_inr,-assoc] end end
  omit K
  variables {D} (d d')

  definition coproduct_object_iso_coproduct_object [constructor] (H₁ H₂ : has_binary_coproducts D) :
    @coproduct_object D H₁ d d' ≅ @coproduct_object D H₂ d d' :=
  colimit_object_iso_colimit_object _ H₁ H₂

  end bin_coproducts

  /-
    intentionally we define coproducts in terms of colimits,
    but coequalizers in terms of equalizers, to see which characterization is more useful
  -/

  section coequalizers
  open bool prod.ops sum equalizer_category_hom

  definition has_coequalizers [reducible] (D : Precategory) := has_equalizers Dᵒᵖ
  variables [K : has_coequalizers D]
  include K

  variables {d d' x : D} (f g : d ⟶ d')
  definition coequalizer_object : D :=
  !(@equalizer_object Dᵒᵖ) f g

  definition coequalizer : d' ⟶ coequalizer_object f g :=
  !(@equalizer Dᵒᵖ)

  theorem coequalizes : coequalizer f g ∘ f = coequalizer f g ∘ g :=
  by rexact !(@equalizes Dᵒᵖ)

  variables {f g}
  definition coequalizer_hom (h : d' ⟶ x) (p : h ∘ f = h ∘ g) : coequalizer_object f g ⟶ x :=
  !(@hom_equalizer Dᵒᵖ) proof p qed

  theorem coequalizer_hom_coequalizer (h : d' ⟶ x) (p : h ∘ f = h ∘ g)
    : coequalizer_hom h p ∘ coequalizer f g = h :=
  by rexact !(@equalizer_hom_equalizer Dᵒᵖ)

  theorem eq_coequalizer_hom {h : d' ⟶ x} (p : h ∘ f = h ∘ g) {i : coequalizer_object f g ⟶ x}
    (q : i ∘ coequalizer f g = h) : i = coequalizer_hom h p :=
  by rexact !(@eq_hom_equalizer Dᵒᵖ) proof q qed

  theorem coequalizer_cocone_unique {h : d' ⟶ x} (p : h ∘ f = h ∘ g)
    {i₁ : coequalizer_object f g ⟶ x} (q₁ : i₁ ∘ coequalizer f g = h)
    {i₂ : coequalizer_object f g ⟶ x} (q₂ : i₂ ∘ coequalizer f g = h) : i₁ = i₂ :=
  !(@equalizer_cone_unique Dᵒᵖ) proof p qed proof q₁ qed proof q₂ qed

  omit K
  variables (f g)
  definition coequalizer_object_iso_coequalizer_object [constructor] (H₁ H₂ : has_coequalizers D) :
    @coequalizer_object D H₁ _ _ f g ≅ @coequalizer_object D H₂ _ _ f g :=
  iso_of_opposite_iso !(@equalizer_object_iso_equalizer_object Dᵒᵖ)

  end coequalizers

  section pushouts
  open bool prod.ops sum pullback_category_hom

  definition has_pushouts [reducible] (D : Precategory) := has_pullbacks Dᵒᵖ
  variables [K : has_pushouts D]
  include K

  variables {d₁ d₂ d₃ x : D} (f : d₁ ⟶ d₂) (g : d₁ ⟶ d₃)
  definition pushout_object : D :=
  !(@pullback_object Dᵒᵖ) f g

  definition pushout : d₃ ⟶ pushout_object f g :=
  !(@pullback Dᵒᵖ)

  definition pushout_rev : d₂ ⟶ pushout_object f g :=
  !(@pullback_rev Dᵒᵖ)

  theorem pushout_commutes : pushout_rev f g ∘ f = pushout f g ∘ g :=
  by rexact !(@pullback_commutes Dᵒᵖ)

  variables {f g}
  definition pushout_hom (h₁ : d₂ ⟶ x) (h₂ : d₃ ⟶ x) (p : h₁ ∘ f = h₂ ∘ g)
    : pushout_object f g ⟶ x :=
  !(@hom_pullback Dᵒᵖ) proof p qed

  theorem pushout_hom_pushout (h₁ : d₂ ⟶ x) (h₂ : d₃ ⟶ x) (p : h₁ ∘ f = h₂ ∘ g)
    : pushout_hom h₁ h₂ p ∘ pushout f g = h₂ :=
  by rexact !(@pullback_hom_pullback Dᵒᵖ)

  theorem pushout_hom_pushout_rev (h₁ : d₂ ⟶ x) (h₂ : d₃ ⟶ x) (p : h₁ ∘ f = h₂ ∘ g)
    : pushout_hom h₁ h₂ p ∘ pushout_rev f g = h₁ :=
  by rexact !(@pullback_rev_hom_pullback Dᵒᵖ)

  theorem eq_pushout_hom {h₁ : d₂ ⟶ x} {h₂ : d₃ ⟶ x} (p : h₁ ∘ f = h₂ ∘ g)
    {i : pushout_object f g ⟶ x} (q : i ∘ pushout f g = h₂) (r : i ∘ pushout_rev f g = h₁)
    : i = pushout_hom h₁ h₂ p :=
  by rexact !(@eq_hom_pullback Dᵒᵖ) proof q qed proof r qed

  theorem pushout_cocone_unique {h₁ : d₂ ⟶ x} {h₂ : d₃ ⟶ x} (p : h₁ ∘ f = h₂ ∘ g)
    {i₁ : pushout_object f g ⟶ x} (q₁ : i₁ ∘ pushout f g = h₂) (r₁ : i₁ ∘ pushout_rev f g = h₁)
    {i₂ : pushout_object f g ⟶ x} (q₂ : i₂ ∘ pushout f g = h₂) (r₂ : i₂ ∘ pushout_rev f g = h₁)
    : i₁ = i₂ :=
  !(@pullback_cone_unique Dᵒᵖ) proof p qed proof q₁ qed proof r₁ qed proof q₂ qed proof r₂ qed

  omit K
  variables (f g)
  definition pushout_object_iso_pushout_object [constructor] (H₁ H₂ : has_pushouts D) :
    @pushout_object D H₁ _ _ _ f g ≅ @pushout_object D H₂ _ _ _ f g :=
  iso_of_opposite_iso !(@pullback_object_iso_pullback_object (Opposite D))

  end pushouts

  definition has_limits_of_shape_op_op [H : has_limits_of_shape D Iᵒᵖᵒᵖ]
    : has_limits_of_shape D I :=
  by induction I with I Is; induction Is; exact H

  namespace ops
  infixr + := coproduct_object
  end ops

end category
