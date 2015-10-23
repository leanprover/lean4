/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Opposite precategory and (TODO) category
-/

import ..nat_trans ..category

open eq functor iso equiv is_equiv nat_trans

namespace category

  definition opposite [reducible] [constructor] {ob : Type} (C : precategory ob) : precategory ob :=
  precategory.mk' (λ a b, hom b a)
                  (λ a b c f g, g ∘ f)
                  (λ a, id)
                  (λ a b c d f g h, !assoc')
                  (λ a b c d f g h, !assoc)
                  (λ a b f, !id_right)
                  (λ a b f, !id_left)
                  (λ a, !id_id)
                  (λ a b, !is_hset_hom)

  definition Opposite [reducible] [constructor] (C : Precategory) : Precategory :=
  precategory.Mk (opposite C)

  infixr `∘op`:60 := @comp _ (opposite _) _ _ _
  postfix `ᵒᵖ`:(max+2) := Opposite

  variables {C D : Precategory} {a b c : C}

  definition compose_op {f : hom a b} {g : hom b c} : f ∘op g = g ∘ f :=
  by reflexivity

  definition opposite_opposite' {ob : Type} (C : precategory ob) : opposite (opposite C) = C :=
  by cases C; apply idp

  definition opposite_opposite : (Cᵒᵖ)ᵒᵖ = C :=
  (ap (Precategory.mk C) (opposite_opposite' C)) ⬝ !Precategory.eta

  theorem opposite_hom_of_eq {ob : Type} [C : precategory ob] {c c' : ob} (p : c = c')
    : @hom_of_eq ob (opposite C) c c' p = inv_of_eq p :=
  by induction p; reflexivity

  theorem opposite_inv_of_eq {ob : Type} [C : precategory ob] {c c' : ob} (p : c = c')
    : @inv_of_eq ob (opposite C) c c' p = hom_of_eq p :=
  by induction p; reflexivity

  definition opposite_functor [constructor] (F : C ⇒ D) : Cᵒᵖ ⇒ Dᵒᵖ :=
  begin
  apply functor.mk,
    intros, apply respect_id F,
    intros, apply @respect_comp C D
  end

  definition opposite_functor_rev [constructor] (F : Cᵒᵖ ⇒ Dᵒᵖ) : C ⇒ D :=
  begin
  apply functor.mk,
    intros, apply respect_id F,
    intros, apply @respect_comp Cᵒᵖ Dᵒᵖ
  end

  postfix `ᵒᵖᶠ`:(max+2) := opposite_functor
  postfix `ᵒᵖ'`:(max+2) := opposite_functor_rev

  definition opposite_rev_opposite_functor (F : Cᵒᵖ ⇒ Dᵒᵖ) : Fᵒᵖ' ᵒᵖᶠ = F :=
  begin
  fapply functor_eq: esimp,
  { intro c c' f, esimp, exact !id_right ⬝ !id_left}
  end

  definition opposite_opposite_rev_functor (F : C ⇒ D) : Fᵒᵖᶠᵒᵖ' = F :=
  begin
  fapply functor_eq: esimp,
  { intro c c' f, esimp, exact !id_leftright}
  end

  definition opposite_nat_trans [constructor] {F G : C ⇒ D} (η : F ⟹ G) : Gᵒᵖᶠ ⟹ Fᵒᵖᶠ :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact !naturality⁻¹},
  end

  definition opposite_rev_nat_trans [constructor] {F G : Cᵒᵖ ⇒ Dᵒᵖ} (η : F ⟹ G) : Gᵒᵖ' ⟹ Fᵒᵖ' :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact !(@naturality Cᵒᵖ Dᵒᵖ)⁻¹},
  end

  definition opposite_nat_trans_rev [constructor] {F G : C ⇒ D} (η : Fᵒᵖᶠ ⟹ Gᵒᵖᶠ) : G ⟹ F :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact !(@naturality Cᵒᵖ Dᵒᵖ _ _ η)⁻¹},
  end

  definition opposite_rev_nat_trans_rev [constructor] {F G : Cᵒᵖ ⇒ Dᵒᵖ} (η : Fᵒᵖ' ⟹ Gᵒᵖ') : G ⟹ F :=
  begin
    fapply nat_trans.mk: esimp,
    { intro c, exact η c},
    { intro c c' f, exact (naturality η f)⁻¹},
  end

  definition opposite_iso [constructor] {ob : Type} [C : precategory ob] {a b : ob}
    (H : @iso _ C a b) : @iso _ (opposite C) a b :=
  begin
    fapply @iso.MK _ (opposite C),
    { exact to_inv H},
    { exact to_hom H},
    { exact to_left_inverse  H},
    { exact to_right_inverse H},
  end

  definition iso_of_opposite_iso [constructor]  {ob : Type} [C : precategory ob] {a b : ob}
    (H : @iso _ (opposite C) a b) : @iso _ C a b :=
  begin
    fapply iso.MK,
    { exact to_inv H},
    { exact to_hom H},
    { exact to_left_inverse  H},
    { exact to_right_inverse H},
  end

  definition opposite_iso_equiv [constructor]  {ob : Type} [C : precategory ob] (a b : ob)
    : @iso _ (opposite C) a b ≃ @iso _ C a b :=
  begin
    fapply equiv.MK,
    { exact iso_of_opposite_iso},
    { exact opposite_iso},
    { intro H, apply iso_eq, reflexivity},
    { intro H, apply iso_eq, reflexivity},
  end

  definition is_univalent_opposite (C : Category) : is_univalent (Opposite C) :=
  begin
    intro x y,
    fapply is_equiv_of_equiv_of_homotopy,
    { refine @eq_equiv_iso C C x y ⬝e _, symmetry, esimp at *, apply opposite_iso_equiv},
    { intro p, induction p, reflexivity}
  end

  definition category_opposite [constructor] (C : Category) : category (Opposite C) :=
  category.mk _ (is_univalent_opposite C)

  definition Category_opposite [constructor] (C : Category) : Category :=
  Category.mk _ (category_opposite C)

end category
