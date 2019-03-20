/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich, Leonardo de Moura
-/
prelude
import init.core init.Function
open Function
universes u v

class Functor (f : Type u → Type v) : Type (max (u+1) v) :=
(map : Π {α β : Type u}, (α → β) → f α → f β)
(mapConst : Π {α β : Type u}, α → f β → f α := λ α β, map ∘ const β)

infixr ` <$> `:100 := Functor.map
infixr ` <$ `:100  := Functor.mapConst

@[reducible] def Functor.mapConstRev {f : Type u → Type v} [Functor f] {α β : Type u} : f β → α → f α :=
λ a b, b <$ a
infixr ` $> `:100  := Functor.mapConstRev

@[reducible] def Functor.mapRev {f : Type u → Type v} [Functor f] {α β : Type u} : f α → (α → β) → f β :=
λ a f, f <$> a
infixl ` <&> `:100  := Functor.mapRev
