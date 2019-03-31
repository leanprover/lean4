/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import init.control.applicative
universes u v

open Function

class HasBind (m : Type u → Type v) :=
(bind : Π {α β : Type u}, m α → (α → m β) → m β)

export HasBind (bind)

infixl ` >>= `:55 := bind

class Monad (m : Type u → Type v) extends Applicative m, HasBind m : Type (max (u+1) v) :=
(map      := λ α β f x, x >>= pure ∘ f)
(seq      := λ α β f x, f >>= (<$> x))
(seqLeft  := λ α β x y, x >>= λ a, y >>= λ _, pure a)
(seqRight := λ α β x y, x >>= λ _, y)


/- We do not add these instances by default because they are rarely needed,
   and could slow down the current type class resolution procedure. -/

def monadInhabited {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] : Inhabited (m α) :=
⟨pure $ default _⟩

def monadInhabited' {α : Type u} {m : Type u → Type v} [Monad m] : Inhabited (α → m α) :=
⟨pure⟩
