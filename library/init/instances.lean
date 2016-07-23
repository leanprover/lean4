/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta.mk_dec_eq_instance init.subtype init.meta.occurrences

open tactic subtype

definition subtype_decidable_eq [instance] {A : Type} {P : A → Prop} [decidable_eq A] : decidable_eq {x \ P x} :=
by mk_dec_eq_instance

definition list_decidable_eq [instance] {A : Type} [decidable_eq A] : decidable_eq (list A) :=
by mk_dec_eq_instance

definition occurrences_decidable_eq [instance] : decidable_eq occurrences :=
by mk_dec_eq_instance

definition unit_decidable_eq [instance] : decidable_eq unit :=
by mk_dec_eq_instance

definition sum_decidable [instance] {A : Type} {B : Type} [decidable_eq A] [decidable_eq B] : decidable_eq (sum A B) :=
by mk_dec_eq_instance
