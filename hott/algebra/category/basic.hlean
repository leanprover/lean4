/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.category.basic
Author: Jakob von Raumer
-/

import algebra.precategory.iso

open iso is_equiv eq is_trunc

-- A category is a precategory extended by a witness
-- that the function from paths to isomorphisms,
-- is an equivalecnce.
namespace category
  definition is_univalent [reducible] {ob : Type} (C : precategory ob) :=
  Π(a b : ob), is_equiv (@iso_of_eq ob C a b)

  structure category [class] (ob : Type) extends parent : precategory ob :=
    (iso_of_path_equiv : is_univalent parent)

  attribute category [multiple-instances]

  abbreviation iso_of_path_equiv := @category.iso_of_path_equiv

  definition category.mk' [reducible] (ob : Type) (C : precategory ob)
    (H : Π (a b : ob), is_equiv (@iso_of_eq ob C a b)) : category ob :=
  precategory.rec_on C category.mk H

  section basic
  variables {ob : Type} [C : category ob]
  include C

  -- Make iso_of_path_equiv a class instance
  -- TODO: Unsafe class instance?
  attribute iso_of_path_equiv [instance]

  definition eq_of_iso [reducible] {a b : ob} : a ≅ b → a = b :=
  iso_of_eq⁻¹ᵉ

  definition is_trunc_1_ob : is_trunc 1 ob :=
  begin
    apply is_trunc_succ_intro, intros [a, b],
    fapply is_trunc_is_equiv_closed,
          exact (@eq_of_iso _ _ a b),
        apply is_equiv_inv,
  end
  end basic

  -- Bundled version of categories
  -- we don't use Category.carrier explicitly, but rather use Precategory.carrier (to_Precategory C)
  structure Category : Type :=
    (carrier : Type)
    (struct : category carrier)

  attribute Category.struct [instance] [coercion]

  definition Category.to_Precategory [coercion] [reducible] (C : Category) : Precategory :=
  Precategory.mk (Category.carrier C) C

  definition category.Mk [reducible] := Category.mk
  definition category.MK [reducible] (C : Precategory)
    (H : is_univalent C) : Category := Category.mk C (category.mk' C C H)

  definition Category.eta (C : Category) : Category.mk C C = C :=
  Category.rec (λob c, idp) C

end category
