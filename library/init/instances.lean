/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta.mk_dec_eq_instance init.subtype init.meta.occurrences init.sum
set_option new_elaborator true
open tactic subtype
universe variables u v

attribute [instance]
definition subtype_decidable_eq {A : Type u} {P : A → Prop} [decidable_eq A] : decidable_eq {x \ P x} :=
by mk_dec_eq_instance

attribute [instance]
definition list_decidable_eq {A : Type u} [decidable_eq A] : decidable_eq (list A) :=
by mk_dec_eq_instance

attribute [instance]
definition occurrences_decidable_eq : decidable_eq occurrences :=
by mk_dec_eq_instance

attribute [instance]
definition unit_decidable_eq : decidable_eq unit :=
by mk_dec_eq_instance

attribute [instance]
definition sum_decidable {A : Type u} {B : Type v} [decidable_eq A] [decidable_eq B] : decidable_eq (A ⊕ B) :=
by mk_dec_eq_instance
