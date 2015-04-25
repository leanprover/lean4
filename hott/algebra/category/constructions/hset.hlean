/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.constructions.hset
Authors: Floris van Doorn, Jakob von Raumer

Category of hsets
-/

import ..category types.equiv

--open eq is_trunc sigma equiv iso is_equiv
open eq category equiv iso is_equiv is_trunc function sigma

namespace category

  definition precategory_hset [reducible] : precategory hset :=
  precategory.mk (λx y : hset, x → y)
                 (λx y z g f a, g (f a))
                 (λx a, a)
                 (λx y z w h g f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))

  definition Precategory_hset [reducible] : Precategory :=
  Precategory.mk hset precategory_hset

  namespace set
    local attribute is_equiv_subtype_eq [instance]
    definition iso_of_equiv {A B : Precategory_hset} (f : A ≃ B) : A ≅ B :=
    iso.MK (to_fun f)
           (equiv.to_inv f)
           (eq_of_homotopy (sect (to_fun f)))
           (eq_of_homotopy (retr (to_fun f)))

    definition equiv_of_iso {A B : Precategory_hset} (f : A ≅ B) : A ≃ B :=
    equiv.MK (to_hom f)
             (iso.to_inv f)
             (ap10 (right_inverse (to_hom f)))
             (ap10 (left_inverse  (to_hom f)))

    definition is_equiv_iso_of_equiv (A B : Precategory_hset) : is_equiv (@iso_of_equiv A B) :=
    adjointify _ (λf, equiv_of_iso f)
                 (λf, iso.eq_mk idp)
                 (λf, equiv.eq_mk idp)
    local attribute is_equiv_iso_of_equiv [instance]

    open sigma.ops
    definition subtype_eq_inv {A : Type} {B : A → Type} [H : Πa, is_hprop (B a)] (u v : Σa, B a)
      : u = v → u.1 = v.1 :=
    (subtype_eq u v)⁻¹ᵉ
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
             (λf, equiv.MK (to_hom f)
                           (iso.to_inv f)
                           (ap10 (right_inverse (to_hom f)))
                           (ap10 (left_inverse  (to_hom f))))
             (λf, iso.eq_mk idp)
             (λf, equiv.eq_mk idp)

    definition equiv_eq_iso (A B : Precategory_hset) : (A ≃ B) = (A ≅ B) :=
    ua !equiv_equiv_iso

    definition is_univalent_hset (A B : Precategory_hset) : is_equiv (@iso_of_eq _ _ A B) :=
    have H : is_equiv (@iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
      @ap _ _ (to_fun (trunctype.sigma_char 0)) A B), from
    @is_equiv_compose _ _ _ _ _
      (@is_equiv_compose _ _ _ _ _
        (@is_equiv_compose _ _ _ _ _
          _
          (@is_equiv_subtype_eq_inv _ _ _ _ _))
        !univalence)
      !is_equiv_iso_of_equiv,
    (iso_of_eq_eq_compose A B)⁻¹ ▹ H
  end set

  definition category_hset [reducible] [instance] : category hset :=
  category.mk precategory_hset set.is_univalent_hset

  definition Category_hset [reducible] : Category :=
  Category.mk hset category_hset

  abbreviation set := Category_hset
end category
