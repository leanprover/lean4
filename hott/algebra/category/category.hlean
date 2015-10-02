/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jakob von Raumer
-/

import .iso

open iso is_equiv equiv eq is_trunc

/-
  A category is a precategory extended by a witness
  that the function from paths to isomorphisms is an equivalence.
-/
namespace category
  /-
    TODO: restructure this. is_univalent should probably be a class with as argument
    (C : Precategory)
  -/
  definition is_univalent [class] {ob : Type} (C : precategory ob) :=
  Π(a b : ob), is_equiv (iso_of_eq : a = b → a ≅ b)

  definition is_equiv_of_is_univalent [instance] {ob : Type} [C : precategory ob]
    [H : is_univalent C] (a b : ob) : is_equiv (iso_of_eq : a = b → a ≅ b) :=
  H a b

  structure category [class] (ob : Type) extends parent : precategory ob :=
  mk' :: (iso_of_path_equiv : is_univalent parent)

  attribute category [multiple_instances]

  abbreviation iso_of_path_equiv := @category.iso_of_path_equiv
  attribute category.iso_of_path_equiv [instance]

  definition category.mk [reducible] [unfold 2] {ob : Type} (C : precategory ob)
    (H : is_univalent C) : category ob :=
  precategory.rec_on C category.mk' H

  section basic
  variables {ob : Type} [C : category ob]
  include C

  -- Make iso_of_path_equiv a class instance
  attribute iso_of_path_equiv [instance]

  definition eq_equiv_iso [constructor] (a b : ob) : (a = b) ≃ (a ≅ b) :=
  equiv.mk iso_of_eq _

  definition eq_of_iso [reducible] {a b : ob} : a ≅ b → a = b :=
  iso_of_eq⁻¹ᶠ

  definition iso_of_eq_eq_of_iso {a b : ob} (p : a ≅ b) : iso_of_eq (eq_of_iso p) = p :=
  right_inv iso_of_eq p

  definition hom_of_eq_eq_of_iso {a b : ob} (p : a ≅ b) : hom_of_eq (eq_of_iso p) = to_hom p :=
  ap to_hom !iso_of_eq_eq_of_iso

  definition inv_of_eq_eq_of_iso {a b : ob} (p : a ≅ b) : inv_of_eq (eq_of_iso p) = to_inv p :=
  ap to_inv !iso_of_eq_eq_of_iso

  theorem eq_of_iso_refl {a : ob}  : eq_of_iso (iso.refl a) = idp :=
  inv_eq_of_eq idp

  definition is_trunc_1_ob : is_trunc 1 ob :=
  begin
    apply is_trunc_succ_intro, intro a b,
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

  definition Category.to_Precategory [constructor] [coercion] [reducible] (C : Category)
    : Precategory :=
  Precategory.mk (Category.carrier C) C

  definition category.Mk [constructor] [reducible] := Category.mk
  definition category.MK [constructor] [reducible] (C : Precategory)
    (H : is_univalent C) : Category := Category.mk C (category.mk C H)

  definition Category.eta (C : Category) : Category.mk C C = C :=
  Category.rec (λob c, idp) C

end category
