/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The Reader monad transformer for passing immutable State.
-/
prelude
import Init.Control.Basic
import Init.Control.Id
import Init.Control.Except
universes u v w

namespace ReaderT

section
variables {ρ : Type u} {m : Type u → Type v} {α : Type u}

@[inline] protected def orElse [Alternative m] {α : Type u} (x₁ x₂ : ReaderT ρ m α) : ReaderT ρ m α :=
  fun s => x₁ s <|> x₂ s

@[inline] protected def failure [Alternative m] {α : Type u} : ReaderT ρ m α :=
  fun s => failure

end

section
variables {ρ : Type u} {m : Type u → Type v} [Monad m] {α β : Type u}

instance [Alternative m] : Alternative (ReaderT ρ m) := {
  failure := ReaderT.failure,
  orElse  := ReaderT.orElse
}

end
end ReaderT

instance (ρ : Type u) (m : Type u → Type v) : MonadControl m (ReaderT ρ m) := {
  stM      := id,
  liftWith := fun f ctx => f fun x => x ctx,
  restoreM := fun x ctx => x,
}

instance ReaderT.tryFinally {m : Type u → Type v} {ρ : Type u} [MonadFinally m] [Monad m] : MonadFinally (ReaderT ρ m) := {
  tryFinally' := fun x h ctx => tryFinally' (x ctx) (fun a? => h a? ctx)
}
