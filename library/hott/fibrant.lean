-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Author: Jeremy Avigad

import data.unit data.bool data.nat
import data.prod data.sum data.sigma

open unit bool nat prod sum sigma

inductive fibrant [class] (T : Type) : Type :=
fibrant_mk : fibrant T

namespace fibrant

axiom unit_fibrant : fibrant unit
axiom nat_fibrant : fibrant nat
axiom bool_fibrant : fibrant bool
axiom sum_fibrant {A B : Type} [C1 : fibrant A] [C2 : fibrant B] : fibrant (A ⊎ B)
axiom prod_fibrant {A B : Type} [C1 : fibrant A] [C2 : fibrant B] : fibrant (A × B)
axiom sigma_fibrant {A : Type} {B : A → Type} [C1 : fibrant A] [C2 : Πx : A, fibrant (B x)] :
  fibrant (Σx : A, B x)
axiom pi_fibrant {A : Type} {B : A → Type} [C1 : fibrant A] [C2 : Πx : A, fibrant (B x)] :
  fibrant (Πx : A, B x)

instance [persistent] unit_fibrant
instance [persistent] nat_fibrant
instance [persistent] bool_fibrant
instance [persistent] sum_fibrant
instance [persistent] prod_fibrant
instance [persistent] sigma_fibrant
instance [persistent] pi_fibrant

end fibrant
