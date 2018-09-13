/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import init.control.applicative
universes u v

open function

class has_bind (m : Type u → Type v) :=
(bind : Π {α β : Type u}, m α → (α → m β) → m β)

export has_bind (bind)

infixl ` >>= `:55 := bind

class monad (m : Type u → Type v) extends applicative m, has_bind m : Type (max (u+1) v) :=
(map := λ α β f x, x >>= pure ∘ f)
(seq := λ α β f x, f >>= (<$> x))
