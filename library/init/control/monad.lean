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
(bind : ∀ {α β : Type u}, m α → (α → m β) → m β)

export HasBind (bind)

infixr >>= := bind

@[inline] def mcomp {α : Type u} {β δ : Type v} {m : Type v → Type w} [HasBind m] (f : α → m β) (g : β → m δ) : α → m δ :=
fun a => f a >>= g

infixr >=> := mcomp

class Monad (m : Type u → Type v) extends Applicative m, HasBind m : Type (max (u+1) v) :=
(map      := fun α β f x => x >>= pure ∘ f)
(seq      := fun α β f x => f >>= (fun y => y <$> x))
(seqLeft  := fun α β x y => x >>= fun a => y >>= fun _ => pure a)
(seqRight := fun α β x y => x >>= fun _ => y)

instance monadInhabited' {α : Type u} {m : Type u → Type v} [Monad m] : Inhabited (α → m α) :=
⟨pure⟩

instance monadInhabited {α : Type u} {m : Type u → Type v} [Monad m] [Inhabited α] : Inhabited (m α) :=
⟨pure $ default _⟩
