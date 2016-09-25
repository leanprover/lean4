/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.monad init.alternative
open list

universe variables u v

@[inline] def list.bind {A : Type u} {B : Type v} (a : list A) (b : A → list B) : list B :=
join (map b a)

@[inline] def list.ret {A : Type u} (a : A) : list A :=
[a]

instance : monad list :=
⟨@map, @list.ret, @list.bind⟩

instance : alternative list :=
⟨@map, @list.ret, @fapp _ _, @nil, @list.append⟩
