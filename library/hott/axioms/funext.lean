-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT

import hott.path hott.equiv
open path

-- Funext
-- ------

-- Define function extensionality as a type class
inductive funext [class] : Type  :=
  mk : (Π (A : Type) (P : A → Type ) (f g : Π x, P x), is_equiv (@apD10 A P f g))
         → funext

namespace funext

  context
    universe variables l k
    parameters [F : funext.{l k}] {A : Type.{l}} {P : A → Type.{k}} (f g : Π x, P x)

    protected definition ap [instance] : is_equiv (@apD10 A P f g) :=
      rec_on F (λ (H : Π A P f g, _), !H)

    definition path_forall : f ∼ g → f ≈ g :=
      @is_equiv.inv _ _ (@apD10 A P f g) ap

  end

  definition path_forall2 [F : funext] {A B : Type} {P : A → B → Type}
      (f g : Πx y, P x y) : (Πx y, f x y ≈ g x y) → f ≈ g :=
    λ E, path_forall f g (λx, path_forall (f x) (g x) (E x))

end funext
