/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import init.category.applicative
universes u v

class has_bind (m : Type u → Type v) :=
(bind : Π {α β : Type u}, m α → (α → m β) → m β)

@[inline] def bind {m : Type u → Type v} [has_bind m] {α β : Type u} : m α → (α → m β) → m β :=
has_bind.bind

@[inline] def has_bind.and_then {α β : Type u} {m : Type u → Type v} [has_bind m] (x : m α) (y : m β) : m β :=
do x, y

infixl ` >>= `:2 := bind
infixl ` >> `:2  := has_bind.and_then

class monad (m : Type u → Type v) extends applicative m, has_bind m : Type (max u+1 v) :=
(map := λ α β f x, bind x $ λ x, pure (f x))
(seq := λ α β f x, bind f $ λ f, map f x)

def return {m : Type u → Type v} [monad m] {α : Type u} : α → m α :=
pure

/- Identical to has_bind.and_then, but it is not inlined. -/
def has_bind.seq {α β : Type u} {m : Type u → Type v} [has_bind m] (x : m α) (y : m β) : m β :=
do x, y
