/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta.mk_dec_eq_instance init.subtype init.meta.occurrences init.sum
open tactic subtype
universe variables u v

instance {A : Type u} {p : A → Prop} [decidable_eq A] : decidable_eq {x : A // p x} :=
by mk_dec_eq_instance

instance {A : Type u} [decidable_eq A] : decidable_eq (list A) :=
by mk_dec_eq_instance

instance : decidable_eq occurrences :=
by mk_dec_eq_instance

instance : decidable_eq unit :=
by mk_dec_eq_instance

instance {A : Type u} {B : Type v} [decidable_eq A] [decidable_eq B] : decidable_eq (A ⊕ B) :=
by mk_dec_eq_instance
