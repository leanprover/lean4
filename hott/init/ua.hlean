/-
Copyright (c) 2014 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Module: init.ua
Author: Jakob von Raumer

Ported from Coq HoTT
-/

prelude
import .equiv
open eq equiv is_equiv

--Ensure that the types compared are in the same universe
section
  universe variable l
  variables {A B : Type.{l}}

  definition is_equiv_tr_of_eq (H : A = B) : is_equiv (transport (λX:Type, X) H) :=
    (@is_equiv_tr Type (λX, X) A B H)

  definition equiv_of_eq (H : A = B) : A ≃ B :=
    equiv.mk _ (is_equiv_tr_of_eq H)

end

axiom univalence (A B : Type) : is_equiv (@equiv_of_eq A B)

attribute univalence [instance]

-- This is the version of univalence axiom we will probably use most often
definition ua {A B : Type} : A ≃ B → A = B :=
(@equiv_of_eq A B)⁻¹

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
