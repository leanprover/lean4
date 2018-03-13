/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The identity monad.
-/
prelude
import init.category.lift
universe u

@[inline] def id_bind {α β : Type u} (x : α) (f : α → id β) : id β := f x

@[inline] instance : monad.{u u} id :=
{ pure := @id, bind := @id_bind }

@[inline] instance : monad_run id id :=
⟨@id⟩
