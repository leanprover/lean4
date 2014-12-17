-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
prelude
import ..path ..equiv
open eq equiv

--Ensure that the types compared are in the same universe
section
  universe variable l
  variables {A B : Type.{l}}

  definition isequiv_path (H : A = B) :=
    (@is_equiv.transport Type (λX, X) A B H)

  definition equiv_path (H : A = B) : A ≃ B :=
    equiv.mk _ (isequiv_path H)

end

axiom ua_is_equiv (A B : Type) : is_equiv (@equiv_path A B)

-- Make the Equivalence given by the axiom an instance
protected definition inst [instance] (A B : Type) : is_equiv (@equiv_path A B) :=
ua_is_equiv A B

-- This is the version of univalence axiom we will probably use most often
definition ua {A B : Type} : A ≃ B →  A = B :=
@is_equiv.inv _ _ (@equiv_path A B) (inst A B)

-- One consequence of UA is that we can transport along equivalencies of types
namespace Equiv
  universe variable l

  protected definition subst (P : Type → Type) {A B : Type.{l}} (H : A ≃ B)
    : P A → P B :=
  eq.transport P (ua H)

  -- We can use this for calculation evironments
  calc_subst subst

end Equiv
