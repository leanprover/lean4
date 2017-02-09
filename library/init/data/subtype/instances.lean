/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.meta.mk_dec_eq_instance init.data.subtype.basic
open tactic subtype
universes u

instance {α : Type u} {p : α → Prop} [decidable_eq α] : decidable_eq {x : α // p x} :=
by mk_dec_eq_instance
