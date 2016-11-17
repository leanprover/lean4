/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta.mk_dec_eq_instance init.subtype init.meta.occurrences init.sum
open tactic subtype
universe variables u v

instance {α : Type u} {p : α → Prop} [decidable_eq α] : decidable_eq {x : α // p x} :=
by mk_dec_eq_instance

instance {α : Type u} [decidable_eq α] : decidable_eq (list α) :=
by mk_dec_eq_instance

instance : decidable_eq occurrences :=
by mk_dec_eq_instance

instance : decidable_eq unit :=
by mk_dec_eq_instance

instance {α : Type u} {β : Type v} [decidable_eq α] [decidable_eq β] : decidable_eq (α ⊕ β) :=
by mk_dec_eq_instance
