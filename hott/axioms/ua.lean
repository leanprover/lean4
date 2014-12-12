-- Copyright (c) 2014 Jakob von Raumer. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jakob von Raumer
-- Ported from Coq HoTT
import hott.path hott.equiv
open path equiv

--Ensure that the types compared are in the same universe
section
  universe variable l
  variables {A B : Type.{l}}

  definition isequiv_path (H : A ≈ B) :=
    (@is_equiv.transport Type (λX, X) A B H)

  definition equiv_path (H : A ≈ B) : A ≃ B :=
    equiv.mk _ (isequiv_path H)

end

inductive ua_type [class] : Type :=
  mk : (Π (A B : Type), is_equiv (@equiv_path A B)) → ua_type

namespace ua_type

  context
    universe k
    parameters [F : ua_type.{k}] {A B: Type.{k}}

    -- Make the Equivalence given by the axiom an instance
    protected definition inst [instance] : is_equiv (@equiv_path.{k} A B) :=
      rec_on F (λ H, H A B)

    -- This is the version of univalence axiom we will probably use most often
    definition ua : A ≃ B →  A ≈ B :=
      @is_equiv.inv _ _ (@equiv_path A B) inst

  end

end ua_type

-- One consequence of UA is that we can transport along equivalencies of types
namespace Equiv
  universe variable l

  protected definition subst [UA : ua_type] (P : Type → Type) {A B : Type.{l}} (H : A ≃ B)
      : P A → P B :=
    path.transport P (ua_type.ua H)

  -- We can use this for calculation evironments
  calc_subst subst

end Equiv
