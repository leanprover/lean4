/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The identity monad.
-/
prelude
import init.control.lift
universe u

@[inline] def id.bind {α β : Type u} (x : α) (f : α → id β) : id β := f x

@[inline] instance : monad.{u u} id :=
{ pure := @id, bind := @id.bind }

@[inline] def id.run {α : Type u} (x : id α) : α := x

@[inline] instance : monadRun id id :=
⟨@id.run⟩
