-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import logic.core.connectives

inductive inhabited (A : Type) : Type :=
inhabited_mk : A → inhabited A

namespace inhabited

definition inhabited_destruct {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

definition Prop_inhabited [instance] : inhabited Prop :=
inhabited_mk true

definition fun_inhabited [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B) :=
inhabited_destruct H (take b, inhabited_mk (λa, b))

definition default (A : Type) {H : inhabited A} : A := inhabited_destruct H (take a, a)

end inhabited
