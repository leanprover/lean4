/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Properties of functors such as adjoint functors, equivalences, faithful or full functors

TODO: Split this file in different files
-/

import .constructions.functor function arity

open category functor nat_trans eq is_trunc iso equiv prod trunc function pi is_equiv

namespace category
  variables {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C}

  -- TODO: define a structure "adjoint" and then define
  -- structure is_left_adjoint (F : C ⇒ D) :=
  --   (G : D ⇒ C) -- G
  --   (is_adjoint : adjoint F G)

  structure is_left_adjoint [class] (F : C ⇒ D) :=
    (G : D ⇒ C)
    (η : 1 ⟹ G ∘f F)
    (ε : F ∘f G ⟹ 1)
    (H : Π(c : C), ε (F c) ∘ F (η c) = ID (F c))
    (K : Π(d : D), G (ε d) ∘ η (G d) = ID (G d))

  abbreviation right_adjoint  [unfold 4] := @is_left_adjoint.G
  abbreviation unit           [unfold 4] := @is_left_adjoint.η
  abbreviation counit         [unfold 4] := @is_left_adjoint.ε
  abbreviation counit_unit_eq [unfold 4] := @is_left_adjoint.H
  abbreviation unit_counit_eq [unfold 4] := @is_left_adjoint.K

  structure is_equivalence [class] (F : C ⇒ D) extends is_left_adjoint F :=
    mk' ::
    (is_iso_unit : is_iso η)
    (is_iso_counit : is_iso ε)

  abbreviation inverse := @is_equivalence.G
  postfix ⁻¹ := inverse
  --a second notation for the inverse, which is not overloaded (there is no unicode superscript F)
  postfix [parsing_only] `⁻¹F`:std.prec.max_plus := inverse

  definition faithful [class] (F : C ⇒ D) := Π⦃c c' : C⦄ ⦃f f' : c ⟶ c'⦄, F f = F f' → f = f'
  definition full [class] (F : C ⇒ D) := Π⦃c c' : C⦄, is_surjective (@(to_fun_hom F) c c')
  definition fully_faithful [class] (F : C ⇒ D) := Π(c c' : C), is_equiv (@(to_fun_hom F) c c')
  definition split_essentially_surjective [class] (F : C ⇒ D) := Π(d : D), Σ(c : C), F c ≅ d
  definition essentially_surjective [class] (F : C ⇒ D) := Π(d : D), ∃(c : C), F c ≅ d
  definition is_weak_equivalence [class] (F : C ⇒ D) := fully_faithful F × essentially_surjective F
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

  definition is_equiv_of_fully_faithful [instance] [reducible] (F : C ⇒ D) [H : fully_faithful F]
    (c c' : C) : is_equiv (@(to_fun_hom F) c c') :=
  !H

  definition hom_inv [reducible] (F : C ⇒ D) [H : fully_faithful F] (c c' : C) (f : F c ⟶ F c')
    : c ⟶ c' :=
  (to_fun_hom F)⁻¹ᶠ f

  definition hom_equiv_F_hom_F [constructor] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ⟶ c') ≃ (F c ⟶ F c') :=
  equiv.mk _ !H

  definition iso_of_F_iso_F (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) (g : F c ≅ F c') : c ≅ c' :=
  begin
    induction g with g G, induction G with h p q, fapply iso.MK,
      { rexact (to_fun_hom F)⁻¹ᶠ g},
      { rexact (to_fun_hom F)⁻¹ᶠ h},
      { exact abstract begin
        apply eq_of_fn_eq_fn' (to_fun_hom F),
        rewrite [respect_comp, respect_id,
                 right_inv (to_fun_hom F), right_inv (to_fun_hom F), p],
        end end},
      { exact abstract begin
        apply eq_of_fn_eq_fn' (to_fun_hom F),
        rewrite [respect_comp, respect_id,
                 right_inv (to_fun_hom F), right_inv (@(to_fun_hom F) c' c), q],
        end end}
  end

  definition iso_equiv_F_iso_F [constructor] (F : C ⇒ D)
    [H : fully_faithful F] (c c' : C) : (c ≅ c') ≃ (F c ≅ F c') :=
  begin
    fapply equiv.MK,
    { exact to_fun_iso F},
    { apply iso_of_F_iso_F},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [iso_of_F_iso_F], apply right_inv end end},
    { exact abstract begin
      intro f, induction f with f F', induction F' with g p q, apply iso_eq,
      esimp [iso_of_F_iso_F], apply right_inv end end},
  end

  definition is_iso_unit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (unit F) :=
  !is_equivalence.is_iso_unit

  definition is_iso_counit [instance] (F : C ⇒ D) [H : is_equivalence F] : is_iso (counit F) :=
  !is_equivalence.is_iso_counit

  definition iso_unit (F : C ⇒ D) [H : is_equivalence F] : F ⁻¹F ∘f F ≅ 1 :=
  (@(iso.mk _) !is_iso_unit)⁻¹ⁱ

  definition iso_counit (F : C ⇒ D) [H : is_equivalence F] : F ∘f F ⁻¹F ≅ 1 :=
  @(iso.mk _) !is_iso_counit

  definition full_of_fully_faithful (H : fully_faithful F) : full F :=
  λc c' g, tr (fiber.mk ((@(to_fun_hom F) c c')⁻¹ᶠ g) !right_inv)

  definition faithful_of_fully_faithful (H : fully_faithful F) : faithful F :=
  λc c' f f' p, is_injective_of_is_embedding p

  definition fully_faithful_of_full_of_faithful (H : faithful F) (K : full F) : fully_faithful F :=
  begin
    intro c c',
    apply is_equiv_of_is_surjective_of_is_embedding,
    { apply is_embedding_of_is_injective,
      intros f f' p, exact H p},
    { apply K}
  end

  definition split_essentially_surjective_of_is_equivalence (F : C ⇒ D) [H : is_equivalence F]
    : split_essentially_surjective F :=
  begin
   intro d, fconstructor,
   { exact F⁻¹ d},
   { exact componentwise_iso (@(iso.mk (counit F)) !is_iso_counit) d}
  end

  definition reflect_is_iso [constructor] (F : C ⇒ D) [H : fully_faithful F] {c c' : C} (f : c ⟶ c')
    [H : is_iso (F f)] : is_iso f :=
  begin
    fconstructor,
    { exact (to_fun_hom F)⁻¹ᶠ (F f)⁻¹},
    { apply eq_of_fn_eq_fn' (to_fun_hom F),
      rewrite [respect_comp,right_inv (to_fun_hom F),respect_id,left_inverse]},
    { apply eq_of_fn_eq_fn' (to_fun_hom F),
      rewrite [respect_comp,right_inv (to_fun_hom F),respect_id,right_inverse]},
  end

  definition reflect_iso [constructor] (F : C ⇒ D) [H : fully_faithful F] {c c' : C}
    (f : F c ≅ F c') : c ≅ c' :=
  begin
    fconstructor,
    { exact (to_fun_hom F)⁻¹ᶠ f},
    { assert H : is_iso (F ((to_fun_hom F)⁻¹ᶠ f)),
      { have H' : is_iso (to_hom f), from _, exact (right_inv (to_fun_hom F) (to_hom f))⁻¹ ▸ H'},
      exact reflect_is_iso F _},
  end

  theorem reflect_inverse (F : C ⇒ D) [H : fully_faithful F] {c c' : C} (f : c ⟶ c')
    [H : is_iso f] : (to_fun_hom F)⁻¹ᶠ (F f)⁻¹ = f⁻¹ :=
  inverse_eq_inverse (idp : to_hom (@(iso.mk f) (reflect_is_iso F f)) = f)
end category

namespace category
  section
    parameters {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C} (η : G ∘f F ≅ 1) (ε : F ∘f G ≅ 1)

     -- variables (η : Πc, G (F c) ≅ c) (ε : Πd, F (G d) ≅ d)
     -- (pη : Π(c c' : C) (f : hom c c'), f ∘ to_hom (η c) = to_hom (η c') ∘ G (F f))
     -- (pε : Π⦃d d' : D⦄ (f : hom d d'), f ∘ to_hom (ε d) = to_hom (ε d') ∘ F (G f))

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

  theorem is_hprop_is_left_adjoint [instance] {C : Category} {D : Precategory} (F : C ⇒ D)
    : is_hprop (is_left_adjoint F) :=
  begin
    apply is_hprop.mk,
    intro G G', cases G with G η ε H K, cases G' with G' η' ε' H' K',
    assert lem₁ : Π(p : G = G'), p ▸ η = η' → p ▸ ε = ε'
      → is_left_adjoint.mk G η ε H K = is_left_adjoint.mk G' η' ε' H' K',
    { intros p q r, induction p, induction q, induction r, esimp,
      apply apd011 (is_left_adjoint.mk G η ε) !is_hprop.elim !is_hprop.elim},
    assert lem₂ : Π (d : carrier D),
                    (to_fun_hom G (natural_map ε' d) ∘
                    natural_map η (to_fun_ob G' d)) ∘
                    to_fun_hom G' (natural_map ε d) ∘
                    natural_map η' (to_fun_ob G d) = id,
    { intro d, esimp,
      rewrite [assoc],
      rewrite [-assoc (G (ε' d))],
      esimp, rewrite [nf_fn_eq_fn_nf_pt' G' ε η d],
      esimp, rewrite [assoc],
      esimp, rewrite [-assoc],
      rewrite [↑functor.compose, -respect_comp G],
      rewrite [nf_fn_eq_fn_nf_pt ε ε' d,nf_fn_eq_fn_nf_pt η' η (G d),▸*],
      rewrite [respect_comp G],
      rewrite [assoc,▸*,-assoc (G (ε d))],
      rewrite [↑functor.compose, -respect_comp G],
      rewrite [H' (G d)],
      rewrite [respect_id,▸*,id_right],
      apply K},
    assert lem₃ : Π (d : carrier D),
                    (to_fun_hom G' (natural_map ε d) ∘
                    natural_map η' (to_fun_ob G d)) ∘
                    to_fun_hom G (natural_map ε' d) ∘
                    natural_map η (to_fun_ob G' d) = id,
    { intro d, esimp,
      rewrite [assoc, -assoc (G' (ε d))],
      esimp, rewrite [nf_fn_eq_fn_nf_pt' G ε' η' d],
      esimp, rewrite [assoc], esimp, rewrite [-assoc],
      rewrite [↑functor.compose, -respect_comp G'],
      rewrite [nf_fn_eq_fn_nf_pt ε' ε d,nf_fn_eq_fn_nf_pt η η' (G' d)],
      esimp,
      rewrite [respect_comp G'],
      rewrite [assoc,▸*,-assoc (G' (ε' d))],
      rewrite [↑functor.compose, -respect_comp G'],
      rewrite [H (G' d)],
      rewrite [respect_id,▸*,id_right],
      apply K'},
    fapply lem₁,
    { fapply functor.eq_of_pointwise_iso,
      { fapply change_natural_map,
        { exact (G' ∘fn1 ε) ∘n !assoc_natural_rev ∘n (η' ∘1nf G)},
        { intro d, exact (G' (ε d) ∘ η' (G d))},
        { intro d, exact ap (λx, _ ∘ x) !id_left}},
      { intro d, fconstructor,
        { exact (G (ε' d) ∘ η (G' d))},
        { exact lem₂ d },
        { exact lem₃ d }}},
    { clear lem₁, refine transport_hom_of_eq_right _ η ⬝ _,
      krewrite hom_of_eq_compose_right,
      rewrite functor.hom_of_eq_eq_of_pointwise_iso,
      apply nat_trans_eq, intro c, esimp,
      refine !assoc⁻¹ ⬝ ap (λx, _ ∘ x) (nf_fn_eq_fn_nf_pt η η' c) ⬝ !assoc ⬝ _,
      esimp, rewrite [-respect_comp G',H c,respect_id G',▸*,id_left]},
   { clear lem₁, refine transport_hom_of_eq_left _ ε ⬝ _,
     krewrite inv_of_eq_compose_left,
     rewrite functor.inv_of_eq_eq_of_pointwise_iso,
     apply nat_trans_eq, intro d, esimp,
     krewrite [respect_comp],
     rewrite [assoc,nf_fn_eq_fn_nf_pt ε' ε d,-assoc,▸*,H (G' d),id_right]}
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

  theorem is_hprop_fully_faithful [instance] (F : C ⇒ D) : is_hprop (fully_faithful F) :=
  by unfold fully_faithful; exact _

  theorem is_hprop_full [instance] (F : C ⇒ D) : is_hprop (full F) :=
  by unfold full; exact _

  theorem is_hprop_faithful [instance] (F : C ⇒ D) : is_hprop (faithful F) :=
  by unfold faithful; exact _

  theorem is_hprop_essentially_surjective [instance] (F : C ⇒ D)
    : is_hprop (essentially_surjective F) :=
  by unfold essentially_surjective; exact _

  theorem is_hprop_is_weak_equivalence [instance] (F : C ⇒ D) : is_hprop (is_weak_equivalence F) :=
  by unfold is_weak_equivalence; exact _

  theorem is_hprop_is_isomorphism [instance] (F : C ⇒ D) : is_hprop (is_isomorphism F) :=
  by unfold is_isomorphism; exact _

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  equiv_of_is_hprop (λH, (faithful_of_fully_faithful H, full_of_fully_faithful H))
                    (λH, fully_faithful_of_full_of_faithful (pr1 H) (pr2 H))

/- alternative proof using direct calculation with equivalences

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  calc
        fully_faithful F
      ≃ (Π(c c' : C), is_embedding (to_fun_hom F) × is_surjective (to_fun_hom F))
        : pi_equiv_pi_id (λc, pi_equiv_pi_id
            (λc', !is_equiv_equiv_is_embedding_times_is_surjective))
  ... ≃ (Π(c : C), (Π(c' : C), is_embedding  (to_fun_hom F)) ×
                   (Π(c' : C), is_surjective (to_fun_hom F)))
        : pi_equiv_pi_id (λc, !equiv_prod_corec)
  ... ≃ (Π(c c' : C), is_embedding (to_fun_hom F)) × full F
        : equiv_prod_corec
  ... ≃ faithful F × full F
        : prod_equiv_prod_right (pi_equiv_pi_id (λc, pi_equiv_pi_id
            (λc', !is_embedding_equiv_is_injective)))
-/

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
    : is_equivalence F ⁻¹F :=
  is_equivalence.mk F (iso_counit F) (iso_unit F)

/-
  definition is_equivalence_compose (G : D ⇒ E) (F : C ⇒ D)
    [H : is_equivalence G] [K : is_equivalence F] : is_equivalence (G ∘f F) :=
  is_equivalence.mk
    (F ⁻¹F ∘f G ⁻¹F)
    abstract begin
      rewrite [functor.assoc,-functor.assoc F ⁻¹F],
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
