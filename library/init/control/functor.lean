/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
prelude
import init.core init.function init.meta.name
open function
universes u v

class functor (f : Type u → Type v) : Type (max (u+1) v) :=
(map : Π {α β : Type u}, (α → β) → f α → f β)
(map_const : Π {α β : Type u}, α → f β → f α := λ α β, map ∘ const β)

infixr ` <$> `:100 := functor.map
infixr ` <$ `:100  := functor.map_const

@[reducible] def functor.map_const_rev {f : Type u → Type v} [functor f] {α β : Type u} : f β → α → f α :=
λ a b, b <$ a
infixr ` $> `:100  := functor.map_const_rev
