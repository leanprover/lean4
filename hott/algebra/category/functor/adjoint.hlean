/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Adjoint functors
-/

import .attributes .examples

open functor nat_trans is_trunc eq iso prod

namespace category

  structure adjoint {C D : Precategory} (F : C ⇒ D) (G : D ⇒ C) :=
    (η : 1 ⟹ G ∘f F)
    (ε : F ∘f G ⟹ 1)
    (H : Π(c : C), ε (F c) ∘ F (η c) = ID (F c))
    (K : Π(d : D), G (ε d) ∘ η (G d) = ID (G d))

  abbreviation to_unit           [unfold 5] := @adjoint.η
  abbreviation to_counit         [unfold 5] := @adjoint.ε
  abbreviation to_counit_unit_eq [unfold 5] := @adjoint.H
  abbreviation to_unit_counit_eq [unfold 5] := @adjoint.K

  -- TODO: define is_left_adjoint in terms of adjoint:
  -- structure is_left_adjoint (F : C ⇒ D) :=
  --   (G : D ⇒ C) -- G
  --   (is_adjoint : adjoint F G)

  infix ` ⊣ `:55 := adjoint

  structure is_left_adjoint [class] {C D : Precategory} (F : C ⇒ D) :=
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

  section
  universe variables u v w
  parameters {C : Precategory.{u v}} {D : Precategory.{w v}} {F : C ⇒ D} {G : D ⇒ C}
          (θ : hom_functor D ∘f prod_functor_prod Fᵒᵖᶠ 1 ≅ hom_functor C ∘f prod_functor_prod 1 G)
  include θ

  definition adj_unit [constructor] : 1 ⟹ G ∘f F :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact natural_map (to_hom θ) (c, F c) id},
    { intro c c' f,
      note H := naturality (to_hom θ) (ID c, F f),
      note K := ap10 H id,
      rewrite [▸* at K, id_right at K, ▸*, K, respect_id, +id_right],
      clear H K,
      note H := naturality (to_hom θ) (f, ID (F c')),
      note K := ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_left at K, K]}
  end

  definition adj_counit [constructor] : F ∘f G ⟹ 1 :=
  begin
    fapply nat_trans.mk: esimp,
    { intro d, exact natural_map (to_inv θ) (G d, d) id, },
    { intro d d' g,
      note H := naturality (to_inv θ) (Gᵒᵖᶠ g, ID d'),
      note K := ap10 H id,
      rewrite [▸* at K, id_left at K, ▸*, K, respect_id, +id_left],
      clear H K,
      note H := naturality (to_inv θ) (ID (G d), g),
      note K := ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_right at K, K]}
  end

  theorem adj_eq_unit (c : C) (d : D) (f : F c ⟶ d)
    : natural_map (to_hom θ) (c, d) f = G f ∘ adj_unit c :=
  begin
    esimp,
    note H := naturality (to_hom θ) (ID c, f),
    note K := ap10 H id,
    rewrite [▸* at K, id_right at K, K, respect_id, +id_right],
  end

  theorem adj_eq_counit (c : C) (d : D) (g : c ⟶ G d)
    : natural_map (to_inv θ) (c, d) g = adj_counit d ∘ F g :=
  begin
    esimp,
    note H := naturality (to_inv θ) (g, ID d),
    note K := ap10 H id,
    rewrite [▸* at K, id_left at K, K, respect_id, +id_left],
  end

  definition adjoint.mk' [constructor] : F ⊣ G :=
  begin
    fapply adjoint.mk,
    { exact adj_unit},
    { exact adj_counit},
    { intro c, esimp, refine (adj_eq_counit c (F c) (adj_unit c))⁻¹ ⬝ _,
      apply ap10 (to_left_inverse (componentwise_iso θ (c, F c)))},
    { intro d, esimp, refine (adj_eq_unit (G d) d (adj_counit d))⁻¹ ⬝ _,
      apply ap10 (to_right_inverse (componentwise_iso θ (G d, d)))},
  end

  end
/- TODO (below): generalize above definitions to arbitrary categories
  section
  universe variables u₁ u₂ v₁ v₂
  parameters {C : Precategory.{u₁ v₁}} {D : Precategory.{u₂ v₂}} {F : C ⇒ D} {G : D ⇒ C}
          (θ : functor_lift.{v₂ v₁} ∘f hom_functor D ∘f prod_functor_prod Fᵒᵖᶠ 1 ≅
               functor_lift.{v₁ v₂} ∘f hom_functor C ∘f prod_functor_prod 1 G)
  include θ
  open lift
  definition adj_unit [constructor] : 1 ⟹ G ∘f F :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact down (natural_map (to_hom θ) (c, F c) (up id))},
    { intro c c' f,
      let H := naturality (to_hom θ) (ID c, F f),
      let K := ap10 H (up id),
      rewrite [▸* at K, id_right at K, ▸*, K, respect_id, +id_right],
      clear H K,
      let H := naturality (to_hom θ) (f, ID (F c')),
      let K := ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_left at K, K]}
  end

  definition adj_counit [constructor] : F ∘f G ⟹ 1 :=
  begin
    fapply nat_trans.mk: esimp,
    { intro d, exact natural_map (to_inv θ) (G d, d) id, },
    { intro d d' g,
      let H := naturality (to_inv θ) (Gᵒᵖᶠ g, ID d'),
      let K := ap10 H id,
      rewrite [▸* at K, id_left at K, ▸*, K, respect_id, +id_left],
      clear H K,
      let H := naturality (to_inv θ) (ID (G d), g),
      let K := ap10 H id,
      rewrite [▸* at K, respect_id at K,+id_right at K, K]}
  end

  theorem adj_eq_unit (c : C) (d : D) (f : F c ⟶ d)
    : natural_map (to_hom θ) (c, d) (up f) = G f ∘ adj_unit c :=
  begin
    esimp,
    let H := naturality (to_hom θ) (ID c, f),
    let K := ap10 H id,
    rewrite [▸* at K, id_right at K, K, respect_id, +id_right],
  end

  theorem adj_eq_counit (c : C) (d : D) (g : c ⟶ G d)
    : natural_map (to_inv θ) (c, d) (up g) = adj_counit d ∘ F g :=
  begin
    esimp,
    let H := naturality (to_inv θ) (g, ID d),
    let K := ap10 H id,
    rewrite [▸* at K, id_left at K, K, respect_id, +id_left],
  end

  definition adjoint.mk' [constructor] : F ⊣ G :=
  begin
    fapply adjoint.mk,
    { exact adj_unit},
    { exact adj_counit},
    { intro c, esimp, refine (adj_eq_counit c (F c) (adj_unit c))⁻¹ ⬝ _,
      apply ap10 (to_left_inverse (componentwise_iso θ (c, F c)))},
    { intro d, esimp, refine (adj_eq_unit (G d) d (adj_counit d))⁻¹ ⬝ _,
      apply ap10 (to_right_inverse (componentwise_iso θ (G d, d)))},
  end

  end
-/

  variables {C D : Precategory} {F : C ⇒ D} {G : D ⇒ C}

  definition adjoint_opposite [constructor] (H : F ⊣ G) : Gᵒᵖᶠ ⊣ Fᵒᵖᶠ :=
  begin
    fconstructor,
    { rexact opposite_nat_trans (to_counit H)},
    { rexact opposite_nat_trans (to_unit H)},
    { rexact to_unit_counit_eq H},
    { rexact to_counit_unit_eq H}
  end

  definition adjoint_of_opposite [constructor] (H : Fᵒᵖᶠ ⊣ Gᵒᵖᶠ) : G ⊣ F :=
  begin
    fconstructor,
    { rexact opposite_rev_nat_trans (to_counit H)},
    { rexact opposite_rev_nat_trans (to_unit H)},
    { rexact to_unit_counit_eq H},
    { rexact to_counit_unit_eq H}
  end

end category
