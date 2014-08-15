-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad

import logic.connectives.basic

inductive inhabited (A : Type) : Type :=
| inhabited_intro : A → inhabited A

definition inhabited_elim {A : Type} {B : Type} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited_rec H2 H1

definition inhabited_Prop [instance] : inhabited Prop :=
inhabited_intro true

definition inhabited_fun [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B) :=
inhabited_elim H (take b, inhabited_intro (λa, b))

definition default (A : Type) {H : inhabited A} : A := inhabited_elim H (take a, a)
