/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Limits in a category
-/

import .constructions.cone .constructions.discrete .constructions.product
       .constructions.finite_cats .category .constructions.functor

open is_trunc functor nat_trans eq

namespace category

  variables {ob : Type} [C : precategory ob] {c c' : ob} (D I : Precategory)
  include C

  definition is_terminal [class] (c : ob) := Πd, is_contr (d ⟶ c)
  definition is_contr_of_is_terminal [instance] (c d : ob) [H : is_terminal d]
    : is_contr (c ⟶ d) :=
  H c

  definition terminal_morphism (c c' : ob) [H : is_terminal c'] : c ⟶ c' :=
  !center

  definition hom_terminal_eq [H : is_terminal c'] (f f' : c ⟶ c') : f = f' :=
  !is_hprop.elim

  definition eq_terminal_morphism [H : is_terminal c'] (f : c ⟶ c') : f = terminal_morphism c c' :=
  !is_hprop.elim

  definition terminal_iso_terminal {c c' : ob} (H : is_terminal c) (K : is_terminal c') : c ≅ c' :=
  iso.MK !terminal_morphism !terminal_morphism !hom_terminal_eq !hom_terminal_eq

  local attribute is_terminal [reducible]
  theorem is_hprop_is_terminal [instance] : is_hprop (is_terminal c) :=
  _

  omit C

  structure has_terminal_object [class] (D : Precategory) :=
    (d : D)
    (is_terminal : is_terminal d)

  definition terminal_object [reducible] [unfold 2] := @has_terminal_object.d
  attribute has_terminal_object.is_terminal [instance]

  variable {D}
  definition terminal_object_iso_terminal_object (H₁ H₂ : has_terminal_object D)
    : @terminal_object D H₁ ≅ @terminal_object D H₂ :=
  terminal_iso_terminal (@has_terminal_object.is_terminal D H₁)
                        (@has_terminal_object.is_terminal D H₂)

  theorem is_hprop_has_terminal_object [instance] (D : Category)
    : is_hprop (has_terminal_object D) :=
  begin
    apply is_hprop.mk, intro t₁ t₂, induction t₁ with d₁ H₁, induction t₂ with d₂ H₂,
    assert p : d₁ = d₂,
    { apply eq_of_iso, apply terminal_iso_terminal H₁ H₂},
    induction p, exact ap _ !is_hprop.elim
  end

  variable (D)
  definition has_limits_of_shape [class] := Π(F : I ⇒ D), has_terminal_object (cone F)

  /-
    The next definitions states that a category is complete with respect to diagrams
    in a certain universe. "is_complete.{o₁ h₁ o₂ h₂}" means that D is complete
    with respect to diagrams with shape in Precategory.{o₂ h₂}
  -/

  definition is_complete.{o₁ h₁ o₂ h₂} [class] (D : Precategory.{o₁ h₁}) :=
  Π(I : Precategory.{o₂ h₂}), has_limits_of_shape D I

  definition has_limits_of_shape_of_is_complete [instance] [H : is_complete D] (I : Precategory)
    : has_limits_of_shape D I := H I

  section
    open pi
    theorem is_hprop_has_limits_of_shape [instance] (D : Category) (I : Precategory)
      : is_hprop (has_limits_of_shape D I) :=
    by apply is_trunc_pi; intro F; exact is_hprop_has_terminal_object (Category_cone F)

    local attribute is_complete [reducible]
    theorem is_hprop_is_complete [instance] (D : Category) : is_hprop (is_complete D) := _
  end

  variables {D I}
  definition has_terminal_object_cone [H : has_limits_of_shape D I]
    (F : I ⇒ D) : has_terminal_object (cone F) := H F
  local attribute has_terminal_object_cone [instance]

  variables (F : I ⇒ D) [H : has_limits_of_shape D I] {i j : I}
  include H

  definition limit_cone : cone F := !terminal_object

  definition is_terminal_limit_cone [instance] : is_terminal (limit_cone F) :=
  has_terminal_object.is_terminal _

  definition limit_object : D :=
  cone_obj.c (limit_cone F)

  definition limit_nat_trans : constant_functor I (limit_object F) ⟹ F :=
  cone_obj.η (limit_cone F)

  definition limit_morphism (i : I) : limit_object F ⟶ F i :=
  limit_nat_trans F i

  variable {H}
  theorem limit_commute {i j : I} (f : i ⟶ j)
    : to_fun_hom F f ∘ limit_morphism F i = limit_morphism F j :=
  naturality (limit_nat_trans F) f ⬝ !id_right

  variable [H]
  definition limit_cone_obj [constructor] {d : D} {η : Πi, d ⟶ F i}
    (p : Π⦃i j : I⦄ (f : i ⟶ j), to_fun_hom F f ∘ η i = η j) : cone_obj F :=
  cone_obj.mk d (nat_trans.mk η (λa b f, p f ⬝ !id_right⁻¹))

  variable {H}
  definition hom_limit {d : D} (η : Πi, d ⟶ F i)
    (p : Π⦃i j : I⦄ (f : i ⟶ j), to_fun_hom F f ∘ η i = η j) : d ⟶ limit_object F :=
  cone_hom.f (@(terminal_morphism (limit_cone_obj F p) _) (is_terminal_limit_cone _))

  theorem hom_limit_commute {d : D} (η : Πi, d ⟶ F i)
    (p : Π⦃i j : I⦄ (f : i ⟶ j), to_fun_hom F f ∘ η i = η j) (i : I)
    : limit_morphism F i ∘ hom_limit F η p = η i :=
  cone_hom.p (@(terminal_morphism (limit_cone_obj F p) _) (is_terminal_limit_cone _)) i

  definition limit_cone_hom [constructor] {d : D} {η : Πi, d ⟶ F i}
    (p : Π⦃i j : I⦄ (f : i ⟶ j), to_fun_hom F f ∘ η i = η j) {h : d ⟶ limit_object F}
    (q : Πi, limit_morphism F i ∘ h = η i) : cone_hom (limit_cone_obj F p) (limit_cone F) :=
  cone_hom.mk h q

  variable {F}
  theorem eq_hom_limit {d : D} {η : Πi, d ⟶ F i}
    (p : Π⦃i j : I⦄ (f : i ⟶ j), to_fun_hom F f ∘ η i = η j) {h : d ⟶ limit_object F}
    (q : Πi, limit_morphism F i ∘ h = η i) : h = hom_limit F η p :=
  ap cone_hom.f (@eq_terminal_morphism _ _ _ _ (is_terminal_limit_cone _) (limit_cone_hom F p q))

  theorem limit_cone_unique {d : D} {η : Πi, d ⟶ F i}
    (p : Π⦃i j : I⦄ (f : i ⟶ j), to_fun_hom F f ∘ η i = η j)
    {h₁ : d ⟶ limit_object F} (q₁ : Πi, limit_morphism F i ∘ h₁ = η i)
    {h₂ : d ⟶ limit_object F} (q₂ : Πi, limit_morphism F i ∘ h₂ = η i): h₁ = h₂ :=
  eq_hom_limit p q₁ ⬝ (eq_hom_limit p q₂)⁻¹

  definition limit_hom_limit {F G : I ⇒ D} (η : F ⟹ G) : limit_object F ⟶ limit_object G :=
  hom_limit _ (λi, η i ∘ limit_morphism F i)
              abstract by intro i j f; rewrite [assoc,naturality,-assoc,limit_commute] end

  omit H

-- notation `noinstances` t:max := by+ with_options [elaborator.ignore_instances true] (exact t)
-- definition noinstance (t : tactic) : tactic := with_options [elaborator.ignore_instances true] t

  variable (F)
  definition limit_object_iso_limit_object [constructor] (H₁ H₂ : has_limits_of_shape D I) :
    @(limit_object F) H₁ ≅ @(limit_object F) H₂ :=
  begin
    fapply iso.MK,
    { apply hom_limit, apply @(limit_commute F) H₁},
    { apply @(hom_limit F) H₁, apply limit_commute},
    { exact abstract begin fapply limit_cone_unique,
      { apply limit_commute},
      { intro i, rewrite [assoc, hom_limit_commute], apply hom_limit_commute},
      { intro i, apply id_right} end end},
    { exact abstract begin fapply limit_cone_unique,
      { apply limit_commute},
      { intro i, rewrite [assoc, hom_limit_commute], apply hom_limit_commute},
      { intro i, apply id_right} end end}
  end

  section bin_products
  open bool prod.ops
  definition has_binary_products [reducible] (D : Precategory) := has_limits_of_shape D c2
  variables [K : has_binary_products D] (d d' : D)
  include K

  definition product_object : D :=
  limit_object (c2_functor D d d')

  infixr × := product_object

  definition pr1 : d × d' ⟶ d :=
  limit_morphism (c2_functor D d d') ff

  definition pr2 : d × d' ⟶ d' :=
  limit_morphism (c2_functor D d d') tt

  variables {d d'}
  definition hom_product {x : D} (f : x ⟶ d) (g : x ⟶ d') : x ⟶ d × d' :=
  hom_limit (c2_functor D d d') (bool.rec f g)
    (by intro b₁ b₂ f; induction b₁: induction b₂: esimp at *; try contradiction: apply id_left)

  theorem pr1_hom_product {x : D} (f : x ⟶ d) (g : x ⟶ d') : !pr1 ∘ hom_product f g = f :=
  hom_limit_commute (c2_functor D d d') (bool.rec f g) _ ff

  theorem pr2_hom_product {x : D} (f : x ⟶ d) (g : x ⟶ d') : !pr2 ∘ hom_product f g = g :=
  hom_limit_commute (c2_functor D d d') (bool.rec f g) _ tt

  theorem eq_hom_product {x : D} {f : x ⟶ d} {g : x ⟶ d'} {h : x ⟶ d × d'}
    (p : !pr1 ∘ h = f) (q : !pr2 ∘ h = g) : h = hom_product f g :=
  eq_hom_limit _ (bool.rec p q)

  theorem product_cone_unique {x : D} {f : x ⟶ d} {g : x ⟶ d'}
    {h₁ : x ⟶ d × d'} (p₁ : !pr1 ∘ h₁ = f) (q₁ : !pr2 ∘ h₁ = g)
    {h₂ : x ⟶ d × d'} (p₂ : !pr1 ∘ h₂ = f) (q₂ : !pr2 ∘ h₂ = g) : h₁ = h₂ :=
  eq_hom_product p₁ q₁ ⬝ (eq_hom_product p₂ q₂)⁻¹

  variable (D)
  definition product_functor [constructor] : D ×c D ⇒ D :=
  functor.mk
    (λx, product_object x.1 x.2)
    (λx y f, hom_product (f.1 ∘ !pr1) (f.2 ∘ !pr2))
    abstract begin intro x, symmetry, apply eq_hom_product: apply comp_id_eq_id_comp end end
    abstract begin intro x y z g f, symmetry, apply eq_hom_product,
                   rewrite [assoc,pr1_hom_product,-assoc,pr1_hom_product,assoc],
                   rewrite [assoc,pr2_hom_product,-assoc,pr2_hom_product,assoc] end end
  omit K
  variables {D} (d d')

  definition product_object_iso_product_object [constructor] (H₁ H₂ : has_binary_products D) :
    @product_object D H₁ d d' ≅ @product_object D H₂ d d' :=
  limit_object_iso_limit_object _ H₁ H₂

  end bin_products

  section equalizers
  open bool prod.ops sum equalizer_category_hom
  definition has_equalizers [reducible] (D : Precategory) := has_limits_of_shape D equalizer_category
  variables [K : has_equalizers D]
  include K

  variables {d d' x : D} (f g : d ⟶ d')
  definition equalizer_object : D :=
  limit_object (equalizer_category_functor D f g)

  definition equalizer : equalizer_object f g ⟶ d :=
  limit_morphism (equalizer_category_functor D f g) ff

  theorem equalizes : f ∘ equalizer f g = g ∘ equalizer f g :=
   limit_commute (equalizer_category_functor D f g) (inl f1) ⬝
  (limit_commute (equalizer_category_functor D f g) (inl f2))⁻¹

  variables {f g}
  definition hom_equalizer (h : x ⟶ d) (p : f ∘ h = g ∘ h) : x ⟶ equalizer_object f g :=
  hom_limit (equalizer_category_functor D f g)
            (bool.rec h (g ∘ h))
            begin
              intro b₁ b₂ i; induction i with j j: induction j,
              -- report(?) "esimp" is super slow here
              exact p, reflexivity, apply id_left
            end

  theorem equalizer_hom_equalizer (h : x ⟶ d) (p : f ∘ h = g ∘ h)
    : equalizer f g ∘ hom_equalizer h p = h :=
  hom_limit_commute (equalizer_category_functor D f g) (bool.rec h (g ∘ h)) _ ff

  theorem eq_hom_equalizer {h : x ⟶ d} (p : f ∘ h = g ∘ h) {i : x ⟶ equalizer_object f g}
    (q : equalizer f g ∘ i = h) : i = hom_equalizer h p :=
  eq_hom_limit _ (bool.rec q
    begin
      refine ap (λx, x ∘ i) (limit_commute (equalizer_category_functor D f g) (inl f2))⁻¹ ⬝ _,
      refine !assoc⁻¹ ⬝ _,
      exact ap (λx, _ ∘ x) q
    end)

  theorem equalizer_cone_unique {h : x ⟶ d} (p : f ∘ h = g ∘ h)
    {i₁ : x ⟶ equalizer_object f g} (q₁ : equalizer f g ∘ i₁ = h)
    {i₂ : x ⟶ equalizer_object f g} (q₂ : equalizer f g ∘ i₂ = h) : i₁ = i₂ :=
  eq_hom_equalizer p q₁ ⬝ (eq_hom_equalizer p q₂)⁻¹

  omit K
  variables (f g)
  definition equalizer_object_iso_equalizer_object [constructor] (H₁ H₂ : has_equalizers D) :
    @equalizer_object D H₁ _ _ f g ≅ @equalizer_object D H₂ _ _ f g :=
  limit_object_iso_limit_object _ H₁ H₂

  end equalizers

  section pullbacks
  open sum prod.ops pullback_category_ob pullback_category_hom
  definition has_pullbacks [reducible] (D : Precategory) := has_limits_of_shape D pullback_category
  variables [K : has_pullbacks D]
  include K

  variables {d₁ d₂ d₃ x : D} (f : d₁ ⟶ d₃) (g : d₂ ⟶ d₃)
  definition pullback_object : D :=
  limit_object (pullback_category_functor D f g)

  definition pullback : pullback_object f g ⟶ d₂ :=
  limit_morphism (pullback_category_functor D f g) BL

  definition pullback_rev : pullback_object f g ⟶ d₁ :=
  limit_morphism (pullback_category_functor D f g) TR

  theorem pullback_commutes : f ∘ pullback_rev f g = g ∘ pullback f g :=
   limit_commute (pullback_category_functor D f g) (inl f1) ⬝
  (limit_commute (pullback_category_functor D f g) (inl f2))⁻¹

  variables {f g}
  definition hom_pullback (h₁ : x ⟶ d₁) (h₂ : x ⟶ d₂) (p : f ∘ h₁ = g ∘ h₂)
    : x ⟶ pullback_object f g :=
  hom_limit (pullback_category_functor D f g)
            (pullback_category_ob.rec h₁ h₂ (g ∘ h₂))
            begin
              intro i₁ i₂ k; induction k with j j: induction j,
              exact p, reflexivity, apply id_left
            end

  theorem pullback_hom_pullback (h₁ : x ⟶ d₁) (h₂ : x ⟶ d₂) (p : f ∘ h₁ = g ∘ h₂)
    : pullback f g ∘ hom_pullback h₁ h₂ p = h₂ :=
  hom_limit_commute (pullback_category_functor D f g) (pullback_category_ob.rec h₁ h₂ (g ∘ h₂)) _ BL

  theorem pullback_rev_hom_pullback (h₁ : x ⟶ d₁) (h₂ : x ⟶ d₂) (p : f ∘ h₁ = g ∘ h₂)
    : pullback_rev f g ∘ hom_pullback h₁ h₂ p = h₁ :=
  hom_limit_commute (pullback_category_functor D f g) (pullback_category_ob.rec h₁ h₂ (g ∘ h₂)) _ TR

  theorem eq_hom_pullback {h₁ : x ⟶ d₁} {h₂ : x ⟶ d₂} (p : f ∘ h₁ = g ∘ h₂)
    {k : x ⟶ pullback_object f g} (q : pullback f g ∘ k = h₂) (r : pullback_rev f g ∘ k = h₁)
    : k = hom_pullback h₁ h₂ p :=
  eq_hom_limit _ (pullback_category_ob.rec r q
    begin
      refine ap (λx, x ∘ k) (limit_commute (pullback_category_functor D f g) (inl f2))⁻¹ ⬝ _,
      refine !assoc⁻¹ ⬝ _,
      exact ap (λx, _ ∘ x) q
    end)

  theorem pullback_cone_unique {h₁ : x ⟶ d₁} {h₂ : x ⟶ d₂} (p : f ∘ h₁ = g ∘ h₂)
    {k₁ : x ⟶ pullback_object f g} (q₁ : pullback f g ∘ k₁ = h₂) (r₁ : pullback_rev f g ∘ k₁ = h₁)
    {k₂ : x ⟶ pullback_object f g} (q₂ : pullback f g ∘ k₂ = h₂) (r₂ : pullback_rev f g ∘ k₂ = h₁)
    : k₁ = k₂ :=
  (eq_hom_pullback p q₁ r₁) ⬝ (eq_hom_pullback p q₂ r₂)⁻¹

  variables (f g)
  definition pullback_object_iso_pullback_object [constructor] (H₁ H₂ : has_pullbacks D) :
    @pullback_object D H₁ _ _ _ f g ≅ @pullback_object D H₂ _ _ _ f g :=
  limit_object_iso_limit_object _ H₁ H₂

  end pullbacks

end category
