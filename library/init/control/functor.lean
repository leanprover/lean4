/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
prelude
import init.core init.function
open function
universes u v

class functor (f : Type u → Type v) : Type (max (u+1) v) :=
(map : Π {α β : Type u}, (α → β) → f α → f β)
(mapConst : Π {α β : Type u}, α → f β → f α := λ α β, map ∘ const β)

infixr ` <$> `:100 := functor.map
infixr ` <$ `:100  := functor.mapConst

@[reducible] def functor.mapConstRev {f : Type u → Type v} [functor f] {α β : Type u} : f β → α → f α :=
λ a b, b <$ a
infixr ` $> `:100  := functor.mapConstRev

@[reducible] def functor.mapRev {f : Type u → Type v} [functor f] {α β : Type u} : f α → (α → β) → f β :=
λ a f, f <$> a
infixl ` <&> `:100  := functor.mapRev
