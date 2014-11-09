-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import hott.path hott.equiv
open path Equiv

--Ensure that the types compared are in the same universe
universe variable l
variables (A B : Type.{l})

private definition isequiv_path (H : A ≈ B) :=
  (@IsEquiv.transport Type (λX, X) A B H)

definition equiv_path (H : A ≈ B) : A ≃ B :=
  Equiv.mk _ (isequiv_path A B H)

axiom ua_equiv (A B : Type) : IsEquiv (equiv_path A B)

-- Make the Equivalence given by the axiom an instance
definition ua_inst [instance] {A B : Type} := (@ua_equiv A B)

-- This is the version of univalence axiom we will probably use most often
definition ua {A B : Type} : A ≃ B →  A ≈ B :=
  IsEquiv.inv (@equiv_path A B)

-- One consequence of UA is that we can transport along equivalencies of types
namespace Equiv

  protected definition subst (P : Type → Type) {A B : Type.{l}} (H : A ≃ B)
      : P A → P B :=
    path.transport P (ua H)

  -- We can use this for calculation evironments
  calc_subst subst

end Equiv
