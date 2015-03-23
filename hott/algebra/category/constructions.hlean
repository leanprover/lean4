/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.constructions
Authors: Floris van Doorn
-/

import .basic algebra.precategory.constructions types.equiv types.trunc

--open eq eq.ops equiv category.ops iso category is_trunc
open eq category equiv iso is_equiv category.ops is_trunc iso.iso function sigma

namespace category

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
  category.mk' hset precategory_hset set.is_univalent_hset

  definition Category_hset [reducible] : Category :=
  Category.mk hset category_hset

  namespace ops
    abbreviation set := Category_hset
  end ops

  section functor
    open functor nat_trans

    variables {C : Precategory} {D : Category} {F G : D ^c C}
    definition eq_of_iso_functor_ob (η : F ≅ G) (c : C) : F c = G c :=
    by apply eq_of_iso; apply componentwise_iso; exact η

    local attribute functor.to_fun_hom [quasireducible]
    definition eq_of_iso_functor (η : F ≅ G) : F = G :=
    begin
    fapply functor_eq,
      {exact (eq_of_iso_functor_ob η)},
      {intros (c, c', f), --unfold eq_of_iso_functor_ob, --TODO: report: this fails
        apply concat,
          {apply (ap (λx, to_hom x ∘ to_fun_hom F f ∘ _)), apply (retr iso_of_eq)},
        apply concat,
          {apply (ap (λx, _ ∘ to_fun_hom F f ∘ (to_hom x)⁻¹)), apply (retr iso_of_eq)},
        apply inverse, apply naturality_iso}
    end

    definition iso_of_eq_eq_of_iso_functor (η : F ≅ G) : iso_of_eq (eq_of_iso_functor η) = η :=
    begin
    apply iso.eq_mk,
    apply nat_trans_eq_mk,
    intro c,
    rewrite natural_map_hom_of_eq, esimp {eq_of_iso_functor},
    rewrite ap010_functor_eq, esimp {hom_of_eq,eq_of_iso_functor_ob},
    rewrite (retr iso_of_eq),
    end

    definition eq_of_iso_functor_iso_of_eq (p : F = G) : eq_of_iso_functor (iso_of_eq p) = p :=
    begin
    apply functor_eq2,
    intro c,
    esimp {eq_of_iso_functor},
    rewrite ap010_functor_eq,
    esimp {eq_of_iso_functor_ob},
    rewrite componentwise_iso_iso_of_eq,
    rewrite (sect iso_of_eq)
    end

    definition is_univalent_functor (D : Category) (C : Precategory) : is_univalent (D ^c C) :=
    λF G, adjointify _ eq_of_iso_functor
                       iso_of_eq_eq_of_iso_functor
                       eq_of_iso_functor_iso_of_eq

  end functor

  definition Category_functor_of_precategory (D : Category) (C : Precategory) : Category :=
  category.MK (D ^c C) (is_univalent_functor D C)

  definition Category_functor (D : Category) (C : Category) : Category :=
  Category_functor_of_precategory D C

  namespace ops
    infixr `^c2`:35 := Category_functor
  end ops

end category
