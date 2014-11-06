-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT
import hott.path hott.equiv
open path Equiv

universe l
variables (A B : Type.{l})

private definition isequiv_path (H : A ≈ B) :=
  (@IsEquiv.transport Type (λX, X) A B H)

definition equiv_path (H : A ≈ B) : A ≃ B :=
  Equiv_mk _ (isequiv_path A B H)

axiom ua_equiv (A B : Type) : IsEquiv (equiv_path A B)

definition ua_inst [instance] {A B : Type} := (@ua_equiv A B)

definition ua {A B : Type} (H : A ≃ B) : A ≈ B :=
  IsEquiv.inv (@equiv_path A B) H
