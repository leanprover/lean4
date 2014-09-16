-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import logic.core.connectives

inductive inhabited (A : Type) : Type :=
mk : A → inhabited A

namespace inhabited

definition destruct [protected] {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

definition Prop_inhabited [instance] : inhabited Prop :=
mk true

definition fun_inhabited [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B) :=
destruct H (λb, mk (λa, b))

definition dfun_inhabited [instance] (A : Type) {B : A → Type} (H : Πx, inhabited (B x)) :
  inhabited (Πx, B x) :=
mk (λa, destruct (H a) (λb, b))

definition default (A : Type) {H : inhabited A} : A := destruct H (take a, a)

end inhabited
