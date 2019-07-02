/-
Copyright (c) Luke Nelson and Jared Roesch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Luke Nelson, Jared Roesch, Sebastian Ullrich
-/
prelude
import init.control.applicative
universes u v w

open Function

class HasBind (m : Type u → Type v) :=
(bind : Π {α β : Type u}, m α → (α → m β) → m β)

export HasBind (bind)

infixr >>= := bind

@[inline] def mcomp {α : Type u} {β δ : Type v} {m : Type v → Type w} [HasBind m] (f : α → m β) (g : β → m δ) : α → m δ :=
λ a, f a >>= g

infixr >=> := mcomp

class Monad (m : Type u → Type v) extends Applicative m, HasBind m : Type (max (u+1) v) :=
(map      := λ α β f x, x >>= pure ∘ f)
(seq      := λ α β f x, f >>= (λ y, y <$> x))
(seqLeft  := λ α β x y, x >>= λ a, y >>= λ _, pure a)
(seqRight := λ α β x y, x >>= λ _, y)

instance monadInhabited' {α : Type u} {m : Type u → Type v} [Monad m] : Inhabited (α → m α) :=
⟨pure⟩

instance monadInhabited {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] : Inhabited (m α) :=
⟨pure $ default _⟩
