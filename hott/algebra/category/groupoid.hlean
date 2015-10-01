/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

import .iso ..group

open eq is_trunc iso category algebra nat unit

namespace category

  structure groupoid [class] (ob : Type) extends parent : precategory ob :=
  mk' :: (all_iso : Π ⦃a b : ob⦄ (f : hom a b), @is_iso ob parent a b f)

  abbreviation all_iso := @groupoid.all_iso
  attribute groupoid.all_iso [instance] [priority 100000]

  definition groupoid.mk [reducible] {ob : Type} (C : precategory ob)
    (H : Π (a b : ob) (f : a ⟶ b), is_iso f) : groupoid ob :=
  precategory.rec_on C groupoid.mk' H

  -- We can turn each group into a groupoid on the unit type
  definition groupoid_of_group.{l} (A : Type.{l}) [G : group A] : groupoid.{0 l} unit :=
  begin
    fapply groupoid.mk, fapply precategory.mk,
      intros, exact A,
      intros, apply (@group.is_hset_carrier A G),
      intros [a, b, c, g, h], exact (@group.mul A G g h),
      intro a, exact (@group.one A G),
      intros, exact (@group.mul_assoc A G h g f)⁻¹,
      intros, exact (@group.one_mul A G f),
      intros, exact (@group.mul_one A G f),
      intros, esimp [precategory.mk], apply is_iso.mk,
        apply mul.left_inv,
        apply mul.right_inv,
  end

  definition hom_group {A : Type} [G : groupoid A] (a : A) :
    group (hom a a) :=
  begin
    fapply group.mk,
      intro f g, apply (comp f g),
      apply is_hset_hom,
      intros f g h, apply (assoc f g h)⁻¹,
      apply (ID a),
      intro f, apply id_left,
      intro f, apply id_right,
      intro f, exact (iso.inverse f),
      intro f, exact (iso.left_inverse f),
  end

  definition group_of_is_contr_groupoid {ob : Type} [H : is_contr ob]
    [G : groupoid ob] : group (hom (center ob) (center ob)) := !hom_group
  definition group_of_groupoid_unit [G : groupoid unit] : group (hom ⋆ ⋆) := !hom_group

  -- Bundled version of categories
  -- we don't use Groupoid.carrier explicitly, but rather use Groupoid.carrier (to_Precategory C)
  structure Groupoid : Type :=
    (carrier : Type)
    (struct : groupoid carrier)

  attribute Groupoid.struct [instance] [coercion]

  definition Groupoid.to_Precategory [coercion] [reducible] (C : Groupoid) : Precategory :=
  Precategory.mk (Groupoid.carrier C) C

  definition groupoid.Mk [reducible] := Groupoid.mk
  definition groupoid.MK [reducible] (C : Precategory) (H : Π (a b : C) (f : a ⟶ b), is_iso f)
    : Groupoid :=
  Groupoid.mk C (groupoid.mk C H)

  definition Groupoid.eta (C : Groupoid) : Groupoid.mk C C = C :=
  Groupoid.rec (λob c, idp) C

end category
