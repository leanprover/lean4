-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad, Jakob von Raumer
-- Ported from Coq HoTT
prelude
import ..path ..equiv
open eq

-- Funext
-- ------

-- Define function extensionality as a type class
structure funext [class] : Type  :=
(elim : Π (A : Type) (P : A → Type ) (f g : Π x, P x), is_equiv (@apD10 A P f g))


namespace funext

  attribute elim [instance]

  definition eq_of_homotopy [F : funext] {A : Type} {P : A → Type} {f g : Π x, P x} : f ∼ g → f = g :=
  is_equiv.inv (@apD10 A P f g)

  definition eq_of_homotopy2 [F : funext] {A B : Type} {P : A → B → Type}
      (f g : Πx y, P x y) : (Πx y, f x y = g x y) → f = g :=
    λ E, eq_of_homotopy (λx, eq_of_homotopy (E x))

end funext
