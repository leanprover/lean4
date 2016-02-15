/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Functors which are equivalences or isomorphisms
-/

import .adjoint

open eq functor iso prod nat_trans is_equiv equiv is_trunc

namespace category
  variables {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C}

  structure is_equivalence [class] (F : C ⇒ D) extends is_left_adjoint F :=
    mk' ::
    (is_iso_unit : is_iso η)
    (is_iso_counit : is_iso ε)

  abbreviation inverse := @is_equivalence.G
  postfix ⁻¹ := inverse
  --a second notation for the inverse, which is not overloaded (there is no unicode superscript F)
  postfix [parsing_only] `⁻¹ᴱ`:std.prec.max_plus := inverse

  definition is_isomorphism [class] (F : C ⇒ D) := fully_faithful F × is_equiv (to_fun_ob F)

  structure equivalence (C D : Precategory) :=
    (to_functor : C ⇒ D)
    (struct : is_equivalence to_functor)

  structure isomorphism (C D : Precategory) :=
    (to_functor : C ⇒ D)
    (struct : is_isomorphism to_functor)

  infix ` ≃c `:25 := equivalence
  infix ` ≅c `:25 := isomorphism

  attribute equivalence.struct isomorphism.struct [instance] [priority 1500]
  attribute equivalence.to_functor isomorphism.to_functor [coercion]

  definition is_iso_unit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (unit F) :=
  !is_equivalence.is_iso_unit

  definition is_iso_counit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (counit F) :=
  !is_equivalence.is_iso_counit

  definition iso_unit (F : C ⇒ D) [H : is_equivalence F] : F⁻¹ᴱ ∘f F ≅ 1 :=
  (@(iso.mk _) !is_iso_unit)⁻¹ⁱ

  definition iso_counit (F : C ⇒ D) [H : is_equivalence F] : F ∘f F⁻¹ᴱ ≅ 1 :=
  @(iso.mk _) !is_iso_counit

  definition split_essentially_surjective_of_is_equivalence (F : C ⇒ D)
    [H : is_equivalence F] : split_essentially_surjective F :=
  begin
   intro d, fconstructor,
   { exact F⁻¹ d},
   { exact componentwise_iso (@(iso.mk (counit F)) !is_iso_counit) d}
  end

end category

namespace category
  section
    parameters {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C} (η : G ∘f F ≅ 1) (ε : F ∘f G ≅ 1)

    private definition ηn : 1 ⟹ G ∘f F := to_inv η
    private definition εn : F ∘f G ⟹ 1 := to_hom ε

    private definition ηi (c : C) : G (F c) ≅ c := componentwise_iso η c
    private definition εi (d : D) : F (G d) ≅ d := componentwise_iso ε d

    private definition ηi' (c : C) : G (F c) ≅ c :=
    to_fun_iso G (to_fun_iso F (ηi c)⁻¹ⁱ) ⬝i to_fun_iso G (εi (F c)) ⬝i ηi c

    local attribute ηn εn ηi εi ηi' [reducible]

    private theorem adj_η_natural {c c' : C} (f : hom c c')
      : G (F f) ∘ to_inv (ηi' c) = to_inv (ηi' c') ∘ f :=
    let ηi'_nat : G ∘f F ⟹ 1 :=
    calc
      G ∘f F ⟹ (G ∘f F) ∘f 1        : id_right_natural_rev (G ∘f F)
         ... ⟹ (G ∘f F) ∘f (G ∘f F) : (G ∘f F) ∘fn ηn
         ... ⟹ ((G ∘f F) ∘f G) ∘f F : assoc_natural (G ∘f F) G F
         ... ⟹ (G ∘f (F ∘f G)) ∘f F : assoc_natural_rev G F G ∘nf F
         ... ⟹ (G ∘f 1) ∘f F        : (G ∘fn εn) ∘nf F
         ... ⟹ G ∘f F               : id_right_natural G ∘nf F
         ... ⟹ 1                    : to_hom η
    in
    begin
     refine is_natural_inverse' (G ∘f F) functor.id ηi' ηi'_nat _ f,
     intro c, esimp, rewrite [+id_left,id_right]
    end

    private theorem adjointify_adjH (c : C) :
      to_hom (εi (F c)) ∘ F (to_hom (ηi' c))⁻¹ = id :=
    begin
      rewrite [respect_inv], apply comp_inverse_eq_of_eq_comp,
      rewrite [id_left,↑ηi',+respect_comp,+respect_inv',assoc], apply eq_comp_inverse_of_comp_eq,
      rewrite [↑εi,-naturality_iso_id ε (F c)],
      symmetry, exact naturality εn (F (to_hom (ηi c)))
    end

    private theorem adjointify_adjK (d : D) :
      G (to_hom (εi d)) ∘ to_hom (ηi' (G d))⁻¹ⁱ = id :=
    begin
      apply comp_inverse_eq_of_eq_comp,
      rewrite [id_left,↑ηi',+respect_inv',assoc], apply eq_comp_inverse_of_comp_eq,
      rewrite [↑ηi,-naturality_iso_id η (G d),↑εi,naturality_iso_id ε d],
      exact naturality (to_hom η) (G (to_hom (εi d))),
    end

    parameter (G)
    include η ε
    definition is_equivalence.mk : is_equivalence F :=
    begin
      fapply is_equivalence.mk',
      { exact G},
      { fapply nat_trans.mk,
        { intro c, exact to_inv (ηi' c)},
        { intro c c' f, exact adj_η_natural f}},
      { exact εn},
      { exact adjointify_adjH},
      { exact adjointify_adjK},
      { exact @(is_natural_iso _) (λc, !is_iso_inverse)},
      { unfold εn, apply iso.struct, },
    end

    definition equivalence.MK : C ≃c D :=
    equivalence.mk F is_equivalence.mk
  end

  variables {C D E : Precategory} {F : C ⇒ D}

  --TODO: add variants
  definition unit_eq_counit_inv (F : C ⇒ D) [H : is_equivalence F] (c : C) :
    to_fun_hom F (natural_map (unit F) c) =
    @(is_iso.inverse (counit F (F c))) (@(componentwise_is_iso (counit F)) !is_iso_counit (F c)) :=
  begin
    apply eq_inverse_of_comp_eq_id, apply counit_unit_eq
  end

  definition fully_faithful_of_is_equivalence (F : C ⇒ D) [H : is_equivalence F]
    : fully_faithful F :=
  begin
    intro c c',
    fapply adjointify,
    { intro g, exact natural_map (@(iso.inverse (unit F)) !is_iso_unit) c' ∘ F⁻¹ g ∘ unit F c},
    { intro g, rewrite [+respect_comp,▸*],
      xrewrite [natural_map_inverse (unit F) c', respect_inv'],
      apply inverse_comp_eq_of_eq_comp,
      rewrite [+unit_eq_counit_inv],
      esimp, exact naturality (counit F)⁻¹ _},
    { intro f, xrewrite [▸*,natural_map_inverse (unit F) c'], apply inverse_comp_eq_of_eq_comp,
      apply naturality (unit F)},
  end

  definition is_isomorphism.mk [constructor] {F : C ⇒ D} (G : D ⇒ C)
    (p : G ∘f F = 1) (q : F ∘f G = 1) : is_isomorphism F :=
  begin
    constructor,
    { apply fully_faithful_of_is_equivalence, fapply is_equivalence.mk,
      { exact G},
      { apply iso_of_eq p},
      { apply iso_of_eq q}},
    { fapply adjointify,
      { exact G},
      { exact ap010 to_fun_ob q},
      { exact ap010 to_fun_ob p}}
  end

  definition isomorphism.MK [constructor] (F : C ⇒ D) (G : D ⇒ C)
    (p : G ∘f F = 1) (q : F ∘f G = 1) : C ≅c D :=
  isomorphism.mk F (is_isomorphism.mk G p q)

  definition is_equiv_ob_of_is_isomorphism [instance] [unfold 4] (F : C ⇒ D)
    [H : is_isomorphism F] : is_equiv (to_fun_ob F) :=
  pr2 H

  definition is_fully_faithful_of_is_isomorphism [instance] [unfold 4] (F : C ⇒ D)
    [H : is_isomorphism F] : fully_faithful F :=
  pr1 H

  definition strict_inverse [constructor] (F : C ⇒ D) [H : is_isomorphism F] : D ⇒ C :=
  begin
    fapply functor.mk,
    { intro d, exact (to_fun_ob F)⁻¹ᶠ d},
    { intro d d' g, exact (to_fun_hom F)⁻¹ᶠ (inv_of_eq !right_inv ∘ g ∘ hom_of_eq !right_inv)},
    { intro d, apply inv_eq_of_eq, rewrite [respect_id,id_left], apply left_inverse},
    { intro d₁ d₂ d₃ g₂ g₁, apply inv_eq_of_eq, rewrite [respect_comp F,+right_inv (to_fun_hom F)],
      rewrite [+assoc], esimp, /-apply ap (λx, (x ∘ _) ∘ _), FAILS-/ refine ap (λx, (x ∘ _) ∘ _) _,
      refine !id_right⁻¹ ⬝ _, rewrite [▸*,-+assoc], refine ap (λx, _ ∘ _ ∘ x) _,
      exact !right_inverse⁻¹},
  end

  postfix /-[parsing-only]-/ `⁻¹ˢ`:std.prec.max_plus := strict_inverse

  definition strict_right_inverse (F : C ⇒ D) [H : is_isomorphism F] : F ∘f F⁻¹ˢ = 1 :=
  begin
    fapply functor_eq,
    { intro d, esimp, apply right_inv},
    { intro d d' g,
      rewrite [▸*, right_inv (to_fun_hom F), +assoc],
      rewrite [↑[hom_of_eq,inv_of_eq,iso.to_inv], right_inverse],
      rewrite [id_left], apply comp_inverse_cancel_right},
  end

  definition strict_left_inverse (F : C ⇒ D) [H : is_isomorphism F] : F⁻¹ˢ ∘f F = 1 :=
  begin
    fapply functor_eq,
    { intro d, esimp, apply left_inv},
    { intro d d' g, esimp, apply comp_eq_of_eq_inverse_comp, apply comp_inverse_eq_of_eq_comp,
      apply inv_eq_of_eq, rewrite [+respect_comp,-assoc], apply ap011 (λx y, x ∘ F g ∘ y),
      { rewrite [adj], rewrite [▸*,respect_inv_of_eq F]},
      { rewrite [adj,▸*,respect_hom_of_eq F]}},
  end

  definition is_equivalence_of_is_isomorphism [instance] [constructor] (F : C ⇒ D) [H : is_isomorphism F]
    : is_equivalence F :=
  begin
    fapply is_equivalence.mk,
    { apply F⁻¹ˢ},
    { apply iso_of_eq !strict_left_inverse},
    { apply iso_of_eq !strict_right_inverse},
  end

  definition equivalence_of_isomorphism [constructor] (F : C ≅c D) : C ≃c D :=
  equivalence.mk F _

  theorem is_prop_is_equivalence [instance] {C : Category} {D : Precategory} (F : C ⇒ D)
    : is_prop (is_equivalence F) :=
  begin
    assert f : is_equivalence F ≃ Σ(H : is_left_adjoint F), is_iso (unit F) × is_iso (counit F),
    { fapply equiv.MK,
      { intro H, induction H, fconstructor: constructor, repeat (esimp;assumption) },
      { intro H, induction H with H1 H2, induction H1, induction H2, constructor,
        repeat (esimp at *;assumption)},
      { intro H, induction H with H1 H2, induction H1, induction H2, reflexivity},
      { intro H, induction H, reflexivity}},
    apply is_trunc_equiv_closed_rev, exact f,
  end

  theorem is_prop_is_isomorphism [instance] (F : C ⇒ D) : is_prop (is_isomorphism F) :=
  by unfold is_isomorphism; exact _

  /- closure properties -/

  definition is_isomorphism_id [instance] [constructor] (C : Precategory)
    : is_isomorphism (1 : C ⇒ C) :=
  is_isomorphism.mk 1 !functor.id_right !functor.id_right

  definition is_isomorphism_strict_inverse [constructor] (F : C ⇒ D) [K : is_isomorphism F]
    : is_isomorphism F⁻¹ˢ :=
  is_isomorphism.mk F !strict_right_inverse !strict_left_inverse

  definition is_isomorphism_compose [constructor] (G : D ⇒ E) (F : C ⇒ D)
    [H : is_isomorphism G] [K : is_isomorphism F] : is_isomorphism (G ∘f F) :=
  is_isomorphism.mk
    (F⁻¹ˢ ∘f G⁻¹ˢ)
    abstract begin
      rewrite [functor.assoc,-functor.assoc F⁻¹ˢ,strict_left_inverse,functor.id_right,
               strict_left_inverse]
    end end
    abstract begin
      rewrite [functor.assoc,-functor.assoc G,strict_right_inverse,functor.id_right,
               strict_right_inverse]
    end end

  definition is_equivalence_id [constructor] (C : Precategory) : is_equivalence (1 : C ⇒ C) := _

  definition is_equivalence_inverse [constructor] (F : C ⇒ D) [K : is_equivalence F]
    : is_equivalence F⁻¹ᴱ :=
  is_equivalence.mk F (iso_counit F) (iso_unit F)

  definition is_equivalence_compose [constructor] (G : D ⇒ E) (F : C ⇒ D)
    [H : is_equivalence G] [K : is_equivalence F] : is_equivalence (G ∘f F) :=
  is_equivalence.mk
    (F⁻¹ᴱ ∘f G⁻¹ᴱ)
    abstract begin
      rewrite [functor.assoc,-functor.assoc F⁻¹ᴱ],
      refine ((_ ∘fi !iso_unit) ∘if _) ⬝i _,
      refine (iso_of_eq !functor.id_right ∘if _) ⬝i _,
      apply iso_unit
    end end
    abstract begin
      rewrite [functor.assoc,-functor.assoc G],
      refine ((_ ∘fi !iso_counit) ∘if _) ⬝i _,
      refine (iso_of_eq !functor.id_right ∘if _) ⬝i _,
      apply iso_counit
    end end

  variable (C)
  definition equivalence.refl [refl] [constructor] : C ≃c C :=
  equivalence.mk _ !is_equivalence_id

  definition isomorphism.refl [refl] [constructor] : C ≅c C :=
  isomorphism.mk _ !is_isomorphism_id

  variable {C}

  definition equivalence.symm [symm] [constructor] (H : C ≃c D) : D ≃c C :=
  equivalence.mk _ (is_equivalence_inverse H)

  definition isomorphism.symm [symm] [constructor] (H : C ≅c D) : D ≅c C :=
  isomorphism.mk _ (is_isomorphism_strict_inverse H)

  definition equivalence.trans [trans] [constructor] (H : C ≃c D) (K : D ≃c E) : C ≃c E :=
  equivalence.mk _ (is_equivalence_compose K H)

  definition isomorphism.trans [trans] [constructor] (H : C ≅c D) (K : D ≅c E) : C ≅c E :=
  isomorphism.mk _ (is_isomorphism_compose K H)

  definition equivalence.to_strict_inverse [unfold 3] (H : C ≃c D) : D ⇒ C :=
  H⁻¹ᴱ

  definition isomorphism.to_strict_inverse [unfold 3] (H : C ≅c D) : D ⇒ C :=
  H⁻¹ˢ

  definition is_isomorphism_of_is_equivalence [constructor] {C D : Category} (F : C ⇒ D)
    [H : is_equivalence F] : is_isomorphism F :=
  begin
    fapply is_isomorphism.mk,
    { exact F⁻¹ᴱ},
    { apply eq_of_iso, apply iso_unit},
    { apply eq_of_iso, apply iso_counit},
  end

  definition isomorphism_of_equivalence [constructor] {C D : Category} (F : C ≃c D) : C ≅c D :=
  isomorphism.mk F !is_isomorphism_of_is_equivalence

  definition equivalence_eq {C : Category} {D : Precategory} {F F' : C ≃c D}
    (p : equivalence.to_functor F = equivalence.to_functor F') : F = F' :=
  begin
    induction F, induction F', exact apd011 equivalence.mk p !is_prop.elim
  end

  definition isomorphism_eq {F F' : C ≅c D}
    (p : isomorphism.to_functor F = isomorphism.to_functor F') : F = F' :=
  begin
    induction F, induction F', exact apd011 isomorphism.mk p !is_prop.elim
  end

  definition is_equiv_isomorphism_of_equivalence [constructor] (C D : Category)
    : is_equiv (@equivalence_of_isomorphism C D) :=
  begin
    fapply adjointify,
    { exact isomorphism_of_equivalence},
    { intro F, apply equivalence_eq, reflexivity},
    { intro F, apply isomorphism_eq, reflexivity},
  end

  definition isomorphism_equiv_equivalence [constructor] (C D : Category)
    : (C ≅c D) ≃ (C ≃c D) :=
  equiv.mk _ !is_equiv_isomorphism_of_equivalence

  definition isomorphism_of_eq [constructor] {C D : Precategory} (p : C = D) : C ≅c D :=
  isomorphism.MK (functor_of_eq p)
                 (functor_of_eq p⁻¹)
                 (by induction p; reflexivity)
                 (by induction p; reflexivity)

  definition equiv_ob_of_isomorphism [constructor] {C D : Precategory} (H : C ≅c D) : C ≃ D :=
  equiv.mk H _

  definition equiv_hom_of_isomorphism [constructor] {C D : Precategory} (H : C ≅c D) (c c' : C)
    : c ⟶ c' ≃ H c ⟶ H c' :=
  equiv.mk (to_fun_hom (isomorphism.to_functor H)) _

  /- TODO
  definition is_equiv_isomorphism_of_eq [constructor] (C D : Precategory)
    : is_equiv (@isomorphism_of_eq C D) :=
  begin
    fapply adjointify,
    { intro H, fapply Precategory_eq_of_equiv,
      { apply equiv_ob_of_isomorphism H},
      { exact equiv_hom_of_isomorphism H},
      { /-exact sorry FAILS-/ intros, esimp, apply respect_comp}},
    { intro H, apply isomorphism_eq, esimp, fapply functor_eq: esimp,
      { intro c, exact sorry},
      { exact sorry}},
    { intro p, induction p, esimp, exact sorry},
  end

  definition eq_equiv_isomorphism [constructor] (C D : Precategory)
    : (C = D) ≃ (C ≅c D) :=
  equiv.mk _ !is_equiv_isomorphism_of_eq

  definition equivalence_of_eq [unfold 3] [reducible] {C D : Precategory} (p : C = D) : C ≃c D :=
  equivalence_of_isomorphism (isomorphism_of_eq p)

  definition eq_equiv_equivalence [constructor] (C D : Category) : (C = D) ≃ (C ≃c D) :=
  !eq_equiv_isomorphism ⬝e !isomorphism_equiv_equivalence

  definition is_equivalence_equiv [constructor] (F : C ⇒ D)
    : is_equivalence F ≃ (fully_faithful F × split_essentially_surjective F) :=
  sorry

  definition is_equivalence_equiv_is_weak_equivalence [constructor] {C D : Category}
    (F : C ⇒ D) : is_equivalence F ≃ is_weak_equivalence F :=
  sorry
  -/


/- TODO?
  definition is_isomorphism_equiv1 (F : C ⇒ D) : is_equivalence F
    ≃ Σ(G : D ⇒ C) (η : 1 = G ∘f F) (ε : F ∘f G = 1),
        sorry ⬝ ap (λ(H : C ⇒ C), F ∘f H) η ⬝ sorry = ap (λ(H : D ⇒ D), H ∘f F) ε⁻¹ :=
  sorry

  definition is_isomorphism_equiv2 (F : C ⇒ D) : is_equivalence F
    ≃ ∃(G : D ⇒ C), 1 = G ∘f F × F ∘f G = 1 :=
  sorry
-/

end category
