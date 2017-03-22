/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import init.core init.function init.meta.name
open function
universes u v

section
set_option auto_param.check_exists false

class functor (f : Type u → Type v) : Type (max u+1 v) :=
(map : Π {α β : Type u}, (α → β) → f α → f β)
(infixr ` <$> `:100 := map)
-- ` <$ `
(map_const : Π {α : Type u} (β : Type u), α → f β → f α := λ α β, map ∘ const β)
(map_const_eq : ∀ {α β : Type u}, @map_const α β = map ∘ const β . control_laws_tac)
-- `functor` is indeed a categorical functor
(id_map : Π {α : Type u} (x : f α), id <$> x = x)
(map_comp : Π {α β γ : Type u} (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x)
end

@[inline] def fmap {f : Type u → Type v} [functor f] {α β : Type u} : (α → β) → f α → f β :=
functor.map

@[inline] def fmap_const {f : Type u → Type v} [functor f] {α : Type u} : Π (β : Type u), α → f β → f α :=
functor.map_const

infixr ` <$> `:100 := fmap
infixr ` <$ `:100 := fmap_const
infixr ` $> `:100 := λ α a b, fmap_const α b a
