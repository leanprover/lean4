/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: algebra.groupoid
Author: Jakob von Raumer

Ported from Coq HoTT
-/

import .precategory.iso .group

open eq is_trunc iso category path_algebra nat unit

namespace category

  structure groupoid [class] (ob : Type) extends parent : precategory ob :=
   (all_iso : Π ⦃a b : ob⦄ (f : hom a b), @is_iso ob parent a b f)

  abbreviation all_iso := @groupoid.all_iso
  attribute groupoid.all_iso [instance] [priority 100000]

  definition groupoid.mk' [reducible] (ob : Type) (C : precategory ob)
    (H : Π (a b : ob) (f : a ⟶ b), is_iso f) : groupoid ob :=
  precategory.rec_on C groupoid.mk H

  definition groupoid_of_1_type.{l} (A : Type.{l})
      [H : is_trunc 1 A] : groupoid.{l l} A :=
  groupoid.mk
    (λ (a b : A), a = b)
    (λ (a b : A), have ish : is_hset (a = b), from is_trunc_eq nat.zero a b, ish)
    (λ (a b c : A) (p : b = c) (q : a = b), q ⬝ p)
    (λ (a : A), refl a)
    (λ (a b c d : A) (p : c = d) (q : b = c) (r : a = b), con.assoc r q p)
    (λ (a b : A) (p : a = b), con_idp p)
    (λ (a b : A) (p : a = b), idp_con p)
    (λ (a b : A) (p : a = b), @is_iso.mk A _ a b p p⁻¹
      !con.right_inv !con.left_inv)

  -- A groupoid with a contractible carrier is a group
  definition group_of_is_contr_groupoid {ob : Type} [H : is_contr ob]
    [G : groupoid ob] : group (hom (center ob) (center ob)) :=
  begin
    fapply group.mk,
      intros [f, g], apply (comp f g),
      apply homH,
      intros [f, g, h], apply (assoc f g h)⁻¹,
      apply (ID (center ob)),
      intro f, apply id_left,
      intro f, apply id_right,
      intro f, exact (iso.inverse f),
      intro f, exact (iso.left_inverse f),
  end

  definition group_of_groupoid_unit [G : groupoid unit] : group (hom ⋆ ⋆) :=
  begin
    fapply group.mk,
      intros [f, g], apply (comp f g),
      apply homH,
      intros [f, g, h], apply (assoc f g h)⁻¹,
      apply (ID ⋆),
      intro f, apply id_left,
      intro f, apply id_right,
      intro f, exact (iso.inverse f),
      intro f, exact (iso.left_inverse f),
  end

  -- Conversely we can turn each group into a groupoid on the unit type
  definition groupoid_of_group.{l} (A : Type.{l}) [G : group A] : groupoid.{l l} unit :=
  begin
    fapply groupoid.mk,
      intros, exact A,
      intros, apply (@group.carrier_hset A G),
      intros [a, b, c, g, h], exact (@group.mul A G g h),
      intro a, exact (@group.one A G),
      intros, exact (@group.mul_assoc A G h g f)⁻¹,
      intros, exact (@group.one_mul A G f),
      intros, exact (@group.mul_one A G f),
      intros, apply is_iso.mk,
        apply mul_left_inv,
        apply mul_right_inv,
  end

  protected definition hom_group {A : Type} [G : groupoid A] (a : A) :
    group (hom a a) :=
  begin
    fapply group.mk,
      intros [f, g], apply (comp f g),
      apply homH,
      intros [f, g, h], apply (assoc f g h)⁻¹,
      apply (ID a),
      intro f, apply id_left,
      intro f, apply id_right,
      intro f, exact (iso.inverse f),
      intro f, exact (iso.left_inverse f),
  end

  -- Bundled version of categories
  -- we don't use Groupoid.carrier explicitly, but rather use Groupoid.carrier (to_Precategory C)
  structure Groupoid : Type :=
    (carrier : Type)
    (struct : groupoid carrier)

  attribute Groupoid.struct [instance] [coercion]
  -- definition objects [reducible] := Category.objects
  -- definition category_instance [instance] [coercion] [reducible] := Category.category_instance

  definition Groupoid.to_Precategory [coercion] [reducible] (C : Groupoid) : Precategory :=
  Precategory.mk (Groupoid.carrier C) C

  definition groupoid.Mk [reducible] := Groupoid.mk
  definition groupoid.MK [reducible] (C : Precategory) (H : Π (a b : C) (f : a ⟶ b), is_iso f)
    : Groupoid :=
  Groupoid.mk C (groupoid.mk' C C H)

  definition Groupoid.eta (C : Groupoid) : Groupoid.mk C C = C :=
  Groupoid.rec (λob c, idp) C

end category
