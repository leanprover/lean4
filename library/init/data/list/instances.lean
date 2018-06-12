/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.data.list.basic
import init.control.alternative init.control.monad
open list

universes u v

instance : monad list :=
{ pure := @list.ret, map := @list.map, bind := @list.bind }

instance : alternative list :=
{ failure := @list.nil,
  orelse  := @list.append,
  ..list.monad }
