/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Category of hsets
-/

import ..category types.equiv ..functor types.lift

open eq category equiv iso is_equiv is_trunc function sigma

namespace category

  definition precategory_hset.{u} [reducible] [constructor] : precategory hset.{u} :=
  precategory.mk (λx y : hset, x → y)
                 (λx y z g f a, g (f a))
                 (λx a, a)
                 (λx y z w h g f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))

  definition Precategory_hset [reducible] [constructor] : Precategory :=
  Precategory.mk hset precategory_hset

  namespace set
    local attribute is_equiv_subtype_eq [instance]
    definition iso_of_equiv [constructor] {A B : Precategory_hset} (f : A ≃ B) : A ≅ B :=
    iso.MK (to_fun f)
           (to_inv f)
           (eq_of_homotopy (left_inv (to_fun f)))
           (eq_of_homotopy (right_inv (to_fun f)))

    definition equiv_of_iso [constructor] {A B : Precategory_hset} (f : A ≅ B) : A ≃ B :=
    begin
      apply equiv.MK (to_hom f) (iso.to_inv f),
        exact ap10 (to_right_inverse f),
        exact ap10 (to_left_inverse f)
    end

    definition is_equiv_iso_of_equiv [constructor] (A B : Precategory_hset)
      : is_equiv (@iso_of_equiv A B) :=
    adjointify _ (λf, equiv_of_iso f)
                 (λf, proof iso_eq idp qed)
                 (λf, equiv_eq idp)

    local attribute is_equiv_iso_of_equiv [instance]

    -- TODO: move
    open sigma.ops
    definition subtype_eq_inv {A : Type} {B : A → Type} [H : Πa, is_hprop (B a)] (u v : Σa, B a)
      : u = v → u.1 = v.1 :=
    (subtype_eq u v)⁻¹ᶠ
    local attribute subtype_eq_inv [reducible]
    definition is_equiv_subtype_eq_inv {A : Type} {B : A → Type} [H : Πa, is_hprop (B a)] (u v : Σa, B a)
      : is_equiv (subtype_eq_inv u v) :=
    _

    definition iso_of_eq_eq_compose (A B : hset) : @iso_of_eq _ _ A B =
      @iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
      @ap _ _ (to_fun (trunctype.sigma_char 0)) A B :=
    eq_of_homotopy (λp, eq.rec_on p idp)

    definition equiv_equiv_iso (A B : Precategory_hset) : (A ≃ B) ≃ (A ≅ B) :=
    equiv.MK (λf, iso_of_equiv f)
             (λf, proof equiv.MK (to_hom f)
                           (iso.to_inv f)
                           (ap10 (to_right_inverse f))
                           (ap10 (to_left_inverse  f)) qed)
             (λf, proof iso_eq idp qed)
             (λf, proof equiv_eq idp qed)

    definition equiv_eq_iso (A B : Precategory_hset) : (A ≃ B) = (A ≅ B) :=
    ua !equiv_equiv_iso

    definition is_univalent_hset (A B : Precategory_hset) : is_equiv (iso_of_eq : A = B → A ≅ B) :=
    assert H₁ : is_equiv (@iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
                  @ap _ _ (to_fun (trunctype.sigma_char 0)) A B), from
      @is_equiv_compose _ _ _ _ _
      (@is_equiv_compose _ _ _ _ _
         (@is_equiv_compose _ _ _ _ _
           _
           (@is_equiv_subtype_eq_inv _ _ _ _ _))
         !univalence)
       !is_equiv_iso_of_equiv,
    assert H₂ : _, from (iso_of_eq_eq_compose A B)⁻¹,
    begin
      rewrite H₂ at H₁,
      assumption
    end
  end set

  definition category_hset [instance] [constructor] : category hset :=
  category.mk precategory_hset set.is_univalent_hset

  definition Category_hset [reducible] [constructor] : Category :=
  Category.mk hset category_hset

  abbreviation set [constructor] := Category_hset

  open functor lift
  definition lift_functor.{u v} [constructor] : set.{u} ⇒ set.{max u v} :=
  functor.mk tlift
             (λa b, lift_functor)
             (λa, eq_of_homotopy (λx, by induction x; reflexivity))
             (λa b c g f, eq_of_homotopy (λx, by induction x; reflexivity))
end category
