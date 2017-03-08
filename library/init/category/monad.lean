/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import init.category.applicative
universes u v

class pre_monad (m : Type u → Type v) :=
(bind : Π {α β : Type u}, m α → (α → m β) → m β)

@[inline] def bind {m : Type u → Type v} [pre_monad m] {α β : Type u} : m α → (α → m β) → m β :=
pre_monad.bind

@[inline] def pre_monad.and_then {α β : Type u} {m : Type u → Type v} [pre_monad m] (x : m α) (y : m β) : m β :=
do x, y

infixl ` >>= `:2 := bind
infixl ` >> `:2  := pre_monad.and_then

class monad (m : Type u → Type v) extends applicative m, pre_monad m : Type (max u+1 v) :=
(seq := λ α β f x, bind f $ λ f, bind x $ λ x, pure (f x))
-- implied by `seq`, but a bit simpler
(map := λ α β f x, bind x $ λ x, pure (f x))

def return {m : Type u → Type v} [monad m] {α : Type u} : α → m α :=
pure

/- Identical to pre_monad.and_then, but it is not inlined. -/
def pre_monad.seq {α β : Type u} {m : Type u → Type v} [pre_monad m] (x : m α) (y : m β) : m β :=
do x, y
