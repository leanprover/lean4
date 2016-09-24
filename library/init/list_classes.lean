/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.monad init.alternative
open list

universe variables u v

@[inline] def list_fmap {A : Type u} {B : Type v} (f : A → B) (l : list A) : list B :=
map f l

@[inline] def list_bind {A : Type u} {B : Type v} (a : list A) (b : A → list B) : list B :=
join (map b a)

@[inline] def list_return {A : Type u} (a : A) : list A :=
[a]

instance : monad list :=
⟨@list_fmap, @list_return, @list_bind⟩

instance : alternative list :=
⟨@list_fmap, @list_return, @fapp _ _, @nil, @list.append⟩
