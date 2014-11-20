-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT

-- TODO: take a look at the Coq tricks
import hott.path hott.equiv
open path

set_option pp.universes true

-- Funext
-- ------

-- Define function extensionality as a type class
inductive funext.{l} [class] : Type.{l+3} :=
  mk : (Π {A : Type.{l+1}} {P : A → Type.{l+2}} (f g : Π x, P x), IsEquiv (@apD10 A P f g))
         → funext.{l}

namespace funext

  context
    universe l
    parameters [F : funext.{l}] {A : Type.{l+1}} {P : A → Type.{l+2}} (f g : Π x, P x)

    protected definition apply [instance] : IsEquiv (@apD10 A P f g) :=
      rec_on F (λ H, sorry)

    definition path_forall : f ∼ g → f ≈ g :=
      @IsEquiv.inv _ _ (@apD10 A P f g) apply

  end

  definition path_forall2 [F : funext] {A B : Type} {P : A → B → Type}
      (f g : Πx y, P x y) : (Πx y, f x y ≈ g x y) → f ≈ g :=
    λ E, path_forall f g (λx, path_forall (f x) (g x) (E x))

end funext
