/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.category.monad init.category.alternative init.data.list.basic
import init.meta.mk_dec_eq_instance
open list

universes u v

instance : alternative list :=
⟨@map, @list.ret, @fapp _ _, @nil, @list.append⟩

instance {α : Type u} [decidable_eq α] : decidable_eq (list α) :=
by tactic.mk_dec_eq_instance

instance : decidable_eq string :=
list.decidable_eq
