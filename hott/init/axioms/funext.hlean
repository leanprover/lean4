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
inductive funext [class] : Type  :=
  mk : (Π (A : Type) (P : A → Type ) (f g : Π x, P x), is_equiv (@apD10 A P f g))
         → funext

namespace funext

  universe variables l k
  variables [F : funext.{l k}] {A : Type.{l}} {P : A → Type.{k}}

  include F
  protected definition ap [instance] (f g : Π x, P x) : is_equiv (@apD10 A P f g) :=
    rec_on F (λ(H : Π A P f g, _), !H)

  definition path_pi {f g : Π x, P x} : f ∼ g → f = g :=
  is_equiv.inv (@apD10 A P f g)

  omit F
  definition path_pi2 [F : funext] {A B : Type} {P : A → B → Type}
      (f g : Πx y, P x y) : (Πx y, f x y = g x y) → f = g :=
    λ E, path_pi (λx, path_pi (E x))

end funext
