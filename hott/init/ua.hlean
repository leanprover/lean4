/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Ported from Coq HoTT
-/

prelude
import .equiv
open eq equiv is_equiv

--Ensure that the types compared are in the same universe
section
  universe variable l
  variables {A B : Type.{l}}

  definition is_equiv_cast_of_eq [constructor] (H : A = B) : is_equiv (cast H) :=
  is_equiv_tr (λX, X) H

  definition equiv_of_eq [constructor] (H : A = B) : A ≃ B :=
  equiv.mk _ (is_equiv_cast_of_eq H)

  definition equiv_of_eq_refl [reducible] [unfold_full] (A : Type)
    : equiv_of_eq (refl A) = equiv.refl :=
  idp


end

axiom univalence (A B : Type) : is_equiv (@equiv_of_eq A B)

attribute univalence [instance]

-- This is the version of univalence axiom we will probably use most often
definition ua [reducible] {A B : Type} : A ≃ B → A = B :=
equiv_of_eq⁻¹

definition eq_equiv_equiv (A B : Type) : (A = B) ≃ (A ≃ B) :=
equiv.mk equiv_of_eq _

definition equiv_of_eq_ua [reducible] {A B : Type} (f : A ≃ B) : equiv_of_eq (ua f) = f :=
right_inv equiv_of_eq f

definition cast_ua_fn {A B : Type} (f : A ≃ B) : cast (ua f) = f :=
ap to_fun (equiv_of_eq_ua f)

definition cast_ua {A B : Type} (f : A ≃ B) (a : A) : cast (ua f) a = f a :=
ap10 (cast_ua_fn f) a

definition ua_equiv_of_eq [reducible] {A B : Type} (p : A = B) : ua (equiv_of_eq p) = p :=
left_inv equiv_of_eq p

definition eq_of_equiv_lift {A B : Type} (f : A ≃ B) : A = lift B :=
ua (f ⬝e !equiv_lift)

namespace equiv
  definition ua_refl (A : Type) : ua erfl = idpath A :=
  eq_of_fn_eq_fn !eq_equiv_equiv (right_inv !eq_equiv_equiv erfl)

  -- One consequence of UA is that we can transport along equivalencies of types
  -- We can use this for calculation evironments
  protected definition transport_of_equiv [subst] (P : Type → Type) {A B : Type} (H : A ≃ B)
    : P A → P B :=
  eq.transport P (ua H)

  -- we can "recurse" on equivalences, by replacing them by (equiv_of_eq _)
  definition rec_on_ua [recursor] {A B : Type} {P : A ≃ B → Type}
    (f : A ≃ B) (H : Π(q : A = B), P (equiv_of_eq q)) : P f :=
  right_inv equiv_of_eq f ▸ H (ua f)

  -- a variant where we immediately recurse on the equality in the new goal
  definition rec_on_ua_idp [recursor] {A : Type} {P : Π{B}, A ≃ B → Type} {B : Type}
    (f : A ≃ B) (H : P equiv.refl) : P f :=
  rec_on_ua f (λq, eq.rec_on q H)

  -- a variant where (equiv_of_eq (ua f)) will be replaced by f in the new goal
  definition rec_on_ua' {A B : Type} {P : A ≃ B → A = B → Type}
    (f : A ≃ B) (H : Π(q : A = B), P (equiv_of_eq q) q) : P f (ua f) :=
  right_inv equiv_of_eq f ▸ H (ua f)

  -- a variant where we do both
  definition rec_on_ua_idp' {A : Type} {P : Π{B}, A ≃ B → A = B → Type} {B : Type}
    (f : A ≃ B) (H : P equiv.refl idp) : P f (ua f) :=
  rec_on_ua' f (λq, eq.rec_on q H)

end equiv
