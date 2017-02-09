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

@[inline] def list.bind {α : Type u} {β : Type v} (a : list α) (b : α → list β) : list β :=
join (map b a)

@[inline] def list.ret {α : Type u} (a : α) : list α :=
[a]

instance : monad list :=
{map := @map, ret := @list.ret, bind := @list.bind}

instance : alternative list :=
⟨@map, @list.ret, @fapp _ _, @nil, @list.append⟩

instance {α : Type u} [decidable_eq α] : decidable_eq (list α) :=
by tactic.mk_dec_eq_instance

instance : decidable_eq string :=
list.decidable_eq
