/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.category.lawful
open list

universes u v

local attribute [simp] join list.ret

instance : monad list :=
{ pure := @list.ret, map := @list.map, bind := @list.bind }

instance : alternative list :=
{ failure := @list.nil,
  orelse  := @list.append,
  ..list.monad }
