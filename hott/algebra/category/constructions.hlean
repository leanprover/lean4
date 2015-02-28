/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.constructions
Authors: Floris van Doorn
-/

import .basic algebra.precategory.constructions

--open eq eq.ops equiv category.ops iso category is_trunc
open eq category equiv iso is_equiv category.ops is_trunc iso.iso

--TODO: MOVE THIS
namespace equiv
  variables {A B : Type}
  protected definition eq_mk' {f f' : A → B} [H : is_equiv f] [H' : is_equiv f'] (p : f = f')
      : equiv.mk f H = equiv.mk f' H' :=
  apD011 equiv.mk p sorry --!is_hprop.elim

  protected definition eq_mk {f f' : A ≃ B} (p : to_fun f = to_fun f') : f = f' :=
  by (cases f; cases f'; apply (equiv.eq_mk' p))

end equiv

namespace category

  namespace set
    definition equiv_equiv_iso (A B : Precategory_hset) : (A ≃ B) ≃ (A ≅ B) :=
    equiv.MK (λf, iso.MK (to_fun f)
                         (equiv.to_inv f)
                         (eq_of_homotopy (sect (to_fun f)))
                         (eq_of_homotopy (retr (to_fun f))))
             (λf, equiv.MK (to_hom f)
                           (iso.to_inv f)
                           (ap10 (right_inverse (to_hom f)))
                           (ap10 (left_inverse  (to_hom f))))
             (λf, iso.eq_mk idp)
             (λf, equiv.eq_mk idp)

    definition equiv_eq_iso (A B : Precategory_hset) : (A ≃ B) = (A ≅ B) :=
    ua !equiv_equiv_iso

    definition is_univalent (A B : Precategory_hset) : is_equiv (@iso_of_eq _ _ A B) :=
    sorry
  end set



  definition category_hset [reducible] [instance] : category hset :=
  category.mk' hset precategory_hset set.is_univalent

  definition Category_hset [reducible] : Category :=
  Category.mk hset category_hset

  namespace ops
    abbreviation set := Category_hset
  end ops

end category
