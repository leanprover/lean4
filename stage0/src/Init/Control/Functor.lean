/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Core
open Function
universes u v

class Functor (f : Type u → Type v) : Type (max (u+1) v) :=
(map : ∀ {α β : Type u}, (α → β) → f α → f β)
(mapConst : ∀ {α β : Type u}, α → f β → f α := fun α β => map ∘ const β)

infixr `<$>` := Functor.map
infixr `<$`  := Functor.mapConst

@[reducible] def Functor.mapConstRev {f : Type u → Type v} [Functor f] {α β : Type u} : f β → α → f α :=
fun a b => b <$ a
infixr `$>`  := Functor.mapConstRev

@[reducible] def Functor.mapRev {f : Type u → Type v} [Functor f] {α β : Type u} : f α → (α → β) → f β :=
fun a f => f <$> a
infixl `<&>` := Functor.mapRev
