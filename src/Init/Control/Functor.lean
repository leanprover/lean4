/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Core

open Function
universes u v

@[reducible] def Functor.mapRev {f : Type u → Type v} [Functor f] {α β : Type u} : f α → (α → β) → f β :=
  fun a f => f <$> a

def Functor.discard {f : Type u → Type v} {α : Type u} [Functor f] (x : f α) : f PUnit :=
  Functor.mapConst PUnit.unit x

export Functor (discard)
