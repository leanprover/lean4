----------------------------------------------------------------------------------------------------
-- Copyright (c) 2014 Microsoft Corporation. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Leonardo de Moura, Jeremy Avigad
----------------------------------------------------------------------------------------------------

import logic.connectives.quantifiers

inductive inhabited (A : Type) : Prop :=
| inhabited_intro : A → inhabited A

theorem inhabited_elim {A : Type} {B : Prop} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited_rec H2 H1

theorem inhabited_Prop [instance] : inhabited Prop :=
inhabited_intro true

theorem inhabited_fun [instance] (A : Type) {B : Type} (H : inhabited B) : inhabited (A → B) :=
inhabited_elim H (take b, inhabited_intro (λa, b))

theorem inhabited_exists {A : Type} {p : A → Prop} (H : ∃x, p x) : inhabited A :=
obtain w Hw, from H, inhabited_intro w
