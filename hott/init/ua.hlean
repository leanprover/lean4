/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.ua
Author: Jakob von Raumer

Ported from Coq HoTT
-/

prelude
import .equiv
open eq equiv is_equiv equiv.ops

--Ensure that the types compared are in the same universe
section
  universe variable l
  variables {A B : Type.{l}}

  definition is_equiv_cast_of_eq (H : A = B) : is_equiv (cast H) :=
    (@is_equiv_tr Type (λX, X) A B H)

  definition equiv_of_eq (H : A = B) : A ≃ B :=
    equiv.mk _ (is_equiv_cast_of_eq H)

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


-- One consequence of UA is that we can transport along equivalencies of types
namespace equiv
  universe variable l

  protected definition transport_of_equiv (P : Type → Type) {A B : Type.{l}} (H : A ≃ B)
    : P A → P B :=
  eq.transport P (ua H)

  -- We can use this for calculation evironments
  calc_subst transport_of_equiv

  definition rec_on_of_equiv_of_eq {A B : Type} {P : (A ≃ B) → Type}
    (p : A ≃ B) (H : Π(q : A = B), P (equiv_of_eq q)) : P p :=
  right_inv equiv_of_eq p ▹ H (ua p)

end equiv
