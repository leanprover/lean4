/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/

import algebra.category.constructions function arity

open category functor nat_trans eq is_trunc iso equiv prod trunc function pi is_equiv

namespace category
  variables {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C}

  -- do we want to have a structure "is_adjoint" and define
  -- structure is_left_adjoint (F : C ⇒ D) :=
  --   (right_adjoint : D ⇒ C) -- G
  --   (is_adjoint : adjoint F right_adjoint)

  structure is_left_adjoint [class] (F : C ⇒ D) :=
    (G : D ⇒ C)
    (η : 1 ⟹ G ∘f F)
    (ε : F ∘f G ⟹ 1)
    (H : Π(c : C), (ε (F c)) ∘ (F (η c)) = ID (F c))
    (K : Π(d : D), (G (ε d)) ∘ (η (G d)) = ID (G d))

  abbreviation right_adjoint := @is_left_adjoint.G
  abbreviation unit          := @is_left_adjoint.η
  abbreviation counit        := @is_left_adjoint.ε

  -- structure is_left_adjoint [class] (F : C ⇒ D) :=
  --   (right_adjoint : D ⇒ C) -- G
  --   (unit : functor.id ⟹ right_adjoint ∘f F) -- η
  --   (counit : F ∘f right_adjoint ⟹ functor.id) -- ε
  --   (H : Π(c : C), (counit (F c)) ∘ (F (unit c)) = ID (F c))
  --   (K : Π(d : D), (right_adjoint (counit d)) ∘ (unit (right_adjoint d)) = ID (right_adjoint d))

  structure is_equivalence [class] (F : C ⇒ D) extends is_left_adjoint F :=
    mk' ::
    (is_iso_unit : is_iso η)
    (is_iso_counit : is_iso ε)

  abbreviation inverse := @is_equivalence.G
  postfix `⁻¹` := inverse
  --a second notation for the inverse, which is not overloaded
  postfix [parsing-only] `⁻¹F`:std.prec.max_plus := inverse

  structure equivalence (C D : Precategory) :=
    (to_functor : C ⇒ D)
    (struct : is_equivalence to_functor)

  --TODO: review and change
  definition faithful [class] (F : C ⇒ D) := Π⦃c c' : C⦄ ⦃f f' : c ⟶ c'⦄, F f = F f' → f = f'
  definition full [class] (F : C ⇒ D) := Π⦃c c' : C⦄, is_surjective (@(to_fun_hom F) c c')
  definition fully_faithful [class] (F : C ⇒ D) := Π(c c' : C), is_equiv (@(to_fun_hom F) c c')
  definition split_essentially_surjective [class] (F : C ⇒ D) := Π(d : D), Σ(c : C), F c ≅ d
  definition essentially_surjective [class] (F : C ⇒ D) := Π(d : D), ∃(c : C), F c ≅ d
  definition is_weak_equivalence [class] (F : C ⇒ D) := fully_faithful F × essentially_surjective F
  definition is_isomorphism [class] (F : C ⇒ D) := fully_faithful F × is_equiv (to_fun_ob F)

  structure isomorphism (C D : Precategory) :=
    (to_functor : C ⇒ D)
    (struct : is_isomorphism to_functor)
  --   infix `⊣`:55 := adjoint

  infix `⋍`:25 := equivalence -- \backsimeq or \equiv
  infix `≌`:25 := isomorphism -- \backcong or \iso

  definition is_equiv_of_fully_faithful [instance] (F : C ⇒ D) [H : fully_faithful F] (c c' : C)
    : is_equiv (@(to_fun_hom F) c c') :=
  !H

  definition is_iso_unit [instance] (F : C ⇒ D) (H : is_equivalence F) : is_iso (unit F) :=
  !is_equivalence.is_iso_unit

  definition is_iso_counit [instance] (F : C ⇒ D) (H : is_equivalence F) : is_iso (counit F) :=
  !is_equivalence.is_iso_counit

  -- theorem is_hprop_is_left_adjoint {C : Category} {D : Precategory} (F : C ⇒ D)
  --   : is_hprop (is_left_adjoint F) :=
  -- begin
  --   apply is_hprop.mk,
  --   intro G G', cases G with G η ε H K, cases G' with G' η' ε' H' K',
  --   assert lem : Π(p : G = G'), p ▸ η = η' → p ▸ ε = ε'
  --     → is_left_adjoint.mk G η ε H K = is_left_adjoint.mk G' η' ε' H' K',
  --   { intros p q r, induction p, induction q, induction r, esimp,
  --     apply apd011 (is_left_adjoint.mk G η ε) !is_hprop.elim !is_hprop.elim},
  --   fapply lem,
  --   { fapply functor.eq_of_pointwise_iso,
  --     { fapply change_natural_map,
  --       { exact (G' ∘fn1 ε) ∘n !assoc_natural_rev ∘n (η' ∘1nf G)},
  --       { intro d, exact (G' (ε d) ∘ η' (G d))},
  --       { intro d, exact ap (λx, _ ∘ x) !id_left}},
  --     { intro d, fconstructor,
  --       { exact (G (ε' d) ∘ η (G' d))},
  --       { krewrite [▸*,assoc,-assoc (G (ε' d))],
  --         krewrite [nf_fn_eq_fn_nf_pt' G' ε η d],
  --         krewrite [assoc,-assoc],
  --         rewrite [↑functor.compose, -respect_comp G],
  --         krewrite [nf_fn_eq_fn_nf_pt ε ε' d,nf_fn_eq_fn_nf_pt η' η (G d),▸*],
  --         rewrite [respect_comp G],
  --         krewrite [assoc,-assoc (G (ε d))],
  --         rewrite [↑functor.compose, -respect_comp G],
  --         krewrite [H' (G d)],
  --         rewrite [respect_id,id_right],
  --         apply K},
  --       { krewrite [▸*,assoc,-assoc (G' (ε d))],
  --         krewrite [nf_fn_eq_fn_nf_pt' G ε' η' d],
  --         krewrite [assoc,-assoc],
  --         rewrite [↑functor.compose, -respect_comp G'],
  --         krewrite [nf_fn_eq_fn_nf_pt ε' ε d,nf_fn_eq_fn_nf_pt η η' (G' d),▸*],
  --         rewrite [respect_comp G'],
  --         krewrite [assoc,-assoc (G' (ε' d))],
  --         rewrite [↑functor.compose, -respect_comp G'],
  --         krewrite [H (G' d)],
  --         rewrite [respect_id,id_right],
  --         apply K'}}},
  --   { clear lem, refine transport_hom_of_eq_right _ η ⬝ _,
  --     krewrite hom_of_eq_compose_right,
  --     rewrite functor.hom_of_eq_eq_of_pointwise_iso,
  --     apply nat_trans_eq, intro c, esimp,
  --     refine !assoc⁻¹ ⬝ ap (λx, _ ∘ x) (nf_fn_eq_fn_nf_pt η η' c) ⬝ !assoc ⬝ _,
  --     rewrite [▸*,-respect_comp G',H c,respect_id G',id_left]},
  --   { clear lem, refine transport_hom_of_eq_left _ ε ⬝ _,
  --     krewrite inv_of_eq_compose_left,
  --     rewrite functor.inv_of_eq_eq_of_pointwise_iso,
  --     apply nat_trans_eq, intro d, esimp,
  --     rewrite [respect_comp,assoc,nf_fn_eq_fn_nf_pt ε' ε d,-assoc,▸*,H (G' d),id_right]},
  -- end

  section
    variables (F G)
    variables (η : G ∘f F ≅ 1) (ε : F ∘f G ≅ 1)
    include η ε
    --definition inverse_of_unit_counit

    definition is_equivalence.mk : is_equivalence F :=
    begin
      exact sorry
    end

  end

  definition full_of_fully_faithful (H : fully_faithful F) : full F :=
  λc c', is_surjective.mk (λg, tr (fiber.mk ((@(to_fun_hom F) c c')⁻¹ᶠ g) !right_inv))

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

  definition fully_faithful_of_is_equivalence (F : C ⇒ D) [H : is_equivalence F]
    : fully_faithful F :=
  begin
    intro c c',
    fapply adjointify,
    { intro g, exact natural_map (@(iso.inverse (unit F)) !is_iso_unit) c' ∘ F⁻¹ g ∘ unit F c},
    { intro g, rewrite [+respect_comp], exact sorry},
    { exact sorry},
  end

  definition split_essentially_surjective_of_is_equivalence (F : C ⇒ D) [H : is_equivalence F]
    : split_essentially_surjective F :=
  begin
   intro d, fconstructor,
   { exact F⁻¹ d},
   { exact componentwise_iso (@(iso.mk (counit F)) !is_iso_counit) d}
  end

/-

  definition fully_faithful_equiv (F : C ⇒ D) : fully_faithful F ≃ (faithful F × full F) :=
  sorry

  definition is_equivalence_equiv (F : C ⇒ D)
    : is_equivalence F ≃ (fully_faithful F × split_essentially_surjective F) :=
  sorry

  definition is_hprop_is_weak_equivalence (F : C ⇒ D) : is_hprop (is_weak_equivalence F) :=
  sorry

  definition is_hprop_is_equivalence {C D : Category} (F : C ⇒ D) : is_hprop (is_equivalence F) :=
  sorry

  definition is_equivalence_equiv_is_weak_equivalence {C D : Category} (F : C ⇒ D)
    : is_equivalence F ≃ is_weak_equivalence F :=
  sorry

  definition is_hprop_is_isomorphism (F : C ⇒ D) : is_hprop (is_isomorphism F) :=
  sorry

  definition is_isomorphism_equiv1 (F : C ⇒ D) : is_equivalence F
    ≃ Σ(G : D ⇒ C) (η : 1 = G ∘f F) (ε : F ∘f G = 1),
        sorry ▸ ap (λ(H : C ⇒ C), F ∘f H) η = ap (λ(H : D ⇒ D), H ∘f F) ε⁻¹ :=
  sorry

  definition is_isomorphism_equiv2 (F : C ⇒ D) : is_equivalence F
    ≃ ∃(G : D ⇒ C), 1 = G ∘f F × F ∘f G = 1 :=
  sorry

  definition is_equivalence_of_isomorphism (H : is_isomorphism F) : is_equivalence F :=
  sorry

  definition is_isomorphism_of_is_equivalence {C D : Category} {F : C ⇒ D} (H : is_equivalence F)
    : is_isomorphism F :=
  sorry

  definition isomorphism_of_eq {C D : Precategory} (p : C = D) : C ≌ D :=
  sorry

  definition is_equiv_isomorphism_of_eq (C D : Precategory) : is_equiv (@isomorphism_of_eq C D) :=
  sorry

  definition equivalence_of_eq {C D : Precategory} (p : C = D) : C ⋍ D :=
  sorry

  definition is_equiv_equivalence_of_eq (C D : Category) : is_equiv (@equivalence_of_eq C D) :=
  sorry
-/
end category
