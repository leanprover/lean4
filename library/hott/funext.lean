-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT

-- TODO: move this to an "axioms" folder
-- TODO: take a look at the Coq tricks
import .path .equiv
open path

-- Funext
-- ------

axiom funext {A : Type} {P : A → Type} (f g : Π x : A, P x) : IsEquiv (@apD10 A P f g)

theorem funext_instance [instance] {A : Type} {P : A → Type} (f g : Π x : A, P x) :
    IsEquiv (@apD10 A P f g) :=
  @funext A P f g

definition path_forall {A : Type} {P : A → Type} (f g : Π x : A, P x) : f ∼ g → f ≈ g :=
  IsEquiv.inv !apD10

definition path_forall2 {A B : Type} {P : A → B → Type} (f g : Π x y, P x y) :
  (Πx y, f x y ≈ g x y) → f ≈ g :=
λE, path_forall f g (λx, path_forall (f x) (g x) (E x))
