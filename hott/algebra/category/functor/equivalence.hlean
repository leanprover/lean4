/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Functors which are equivalences or isomorphisms
-/

import .adjoint

open category functor nat_trans eq is_trunc iso equiv prod trunc function pi is_equiv

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
  --   infix `⊣`:55 := adjoint

  infix ` ≃c `:25 := equivalence
  infix ` ≅c `:25 := isomorphism

  definition is_iso_unit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (unit F) :=
  !is_equivalence.is_iso_unit

  definition is_iso_counit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (counit F) :=
  !is_equivalence.is_iso_counit

  definition iso_unit (F : C ⇒ D) [H : is_equivalence F] : F ⁻¹ᴱ ∘f F ≅ 1 :=
  (@(iso.mk _) !is_iso_unit)⁻¹ⁱ

  definition iso_counit (F : C ⇒ D) [H : is_equivalence F] : F ∘f F ⁻¹ᴱ ≅ 1 :=
  @(iso.mk _) !is_iso_counit

  definition split_essentially_surjective_of_is_equivalence (F : C ⇒ D) [H : is_equivalence F]
    : split_essentially_surjective F :=
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
      { exact @(is_iso_nat_trans _) (λc, !is_iso_inverse)},
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

  definition is_isomorphism.mk {F : C ⇒ D} (G : D ⇒ C) (p : G ∘f F = 1) (q : F ∘f G = 1)
    : is_isomorphism F :=
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

  definition is_equiv_of_is_isomorphism (F : C ⇒ D) [H : is_isomorphism F]
    : is_equiv (to_fun_ob F) :=
  pr2 H

  definition is_fully_faithful_of_is_isomorphism (F : C ⇒ D) [H : is_isomorphism F]
    : fully_faithful F :=
  pr1 H

  local attribute is_fully_faithful_of_is_isomorphism is_equiv_of_is_isomorphism [instance]

  definition strict_inverse [constructor] (F : C ⇒ D) [H : is_isomorphism F] : D ⇒ C :=
  begin
    fapply functor.mk,
    { intro d, exact (to_fun_ob F)⁻¹ᶠ d},
    { intro d d' g, exact (to_fun_hom F)⁻¹ᶠ (inv_of_eq !right_inv ∘ g ∘ hom_of_eq !right_inv)},
    { intro d, apply inv_eq_of_eq, rewrite [respect_id,id_left], apply left_inverse},
    { intro d₁ d₂ d₃ g₂ g₁, apply inv_eq_of_eq, rewrite [respect_comp F,+right_inv (to_fun_hom F)],
      rewrite [+assoc], esimp, /-apply ap (λx, _ ∘ x), FAILS-/ refine ap (λx, (x ∘ _) ∘ _) _,
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

  definition is_equivalence_of_is_isomorphism [instance] (F : C ⇒ D) [H : is_isomorphism F]
    : is_equivalence F :=
  begin
    fapply is_equivalence.mk,
    { apply F⁻¹ˢ},
    { apply iso_of_eq !strict_left_inverse},
    { apply iso_of_eq !strict_right_inverse},
  end

  theorem is_hprop_is_equivalence [instance] {C : Category} {D : Precategory} (F : C ⇒ D) : is_hprop (is_equivalence F) :=
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

  theorem is_hprop_is_isomorphism [instance] (F : C ⇒ D) : is_hprop (is_isomorphism F) :=
  by unfold is_isomorphism; exact _

  /- closure properties -/

  definition is_isomorphism_id [instance] (C : Precategory) : is_isomorphism (1 : C ⇒ C) :=
  is_isomorphism.mk 1 !functor.id_right !functor.id_right

  definition is_isomorphism_strict_inverse (F : C ⇒ D) [K : is_isomorphism F]
    : is_isomorphism F⁻¹ˢ :=
  is_isomorphism.mk F !strict_right_inverse !strict_left_inverse

  definition is_isomorphism_compose (G : D ⇒ E) (F : C ⇒ D)
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

  definition is_equivalence_id (C : Precategory) : is_equivalence (1 : C ⇒ C) := _

  definition is_equivalence_strict_inverse (F : C ⇒ D) [K : is_equivalence F]
    : is_equivalence F ⁻¹ᴱ :=
  is_equivalence.mk F (iso_counit F) (iso_unit F)

/-
  definition is_equivalence_compose (G : D ⇒ E) (F : C ⇒ D)
    [H : is_equivalence G] [K : is_equivalence F] : is_equivalence (G ∘f F) :=
  is_equivalence.mk
    (F ⁻¹ᴱ ∘f G ⁻¹ᴱ)
    abstract begin
      rewrite [functor.assoc,-functor.assoc F ⁻¹ᴱ],
--      refine ((_ ∘fi _) ∘if _) ⬝i _,
    end end
    abstract begin
      rewrite [functor.assoc,-functor.assoc G,strict_right_inverse,functor.id_right,
               strict_right_inverse]
    end end

  definition is_equivalence_equiv (F : C ⇒ D)
    : is_equivalence F ≃ (fully_faithful F × split_essentially_surjective F) :=
  sorry

  definition is_isomorphism_equiv1 (F : C ⇒ D) : is_equivalence F
    ≃ Σ(G : D ⇒ C) (η : 1 = G ∘f F) (ε : F ∘f G = 1),
        sorry ▸ ap (λ(H : C ⇒ C), F ∘f H) η = ap (λ(H : D ⇒ D), H ∘f F) ε⁻¹ :=
  sorry

  definition is_isomorphism_equiv2 (F : C ⇒ D) : is_equivalence F
    ≃ ∃(G : D ⇒ C), 1 = G ∘f F × F ∘f G = 1 :=
  sorry

  definition isomorphism_of_eq {C D : Precategory} (p : C = D) : C ≅c D :=
  sorry

  definition is_equiv_isomorphism_of_eq (C D : Precategory) : is_equiv (@isomorphism_of_eq C D) :=
  sorry

  definition equivalence_of_eq {C D : Precategory} (p : C = D) : C ≃c D :=
  sorry

  definition is_isomorphism_of_is_equivalence {C D : Category} {F : C ⇒ D} (H : is_equivalence F)
    : is_isomorphism F :=
  sorry

  definition is_equivalence_equiv_is_weak_equivalence {C D : Category} (F : C ⇒ D)
    : is_equivalence F ≃ is_weak_equivalence F :=
  sorry

  definition is_equiv_equivalence_of_eq (C D : Category) : is_equiv (@equivalence_of_eq C D) :=
  sorry

-/
end category
