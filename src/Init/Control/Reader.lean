/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich

The Reader monad transformer for passing immutable State.
-/
module

prelude
public import Init.Control.Basic
public import Init.Control.Id
public import Init.Control.Except

public section

set_option linter.missingDocs true

namespace ReaderT

/--
Recovers from errors. The same local value is provided to both branches. Typically used via the
`<|>` operator.
-/
@[always_inline, inline]
protected def orElse [Alternative m] (x₁ : ReaderT ρ m α) (x₂ : Unit → ReaderT ρ m α) : ReaderT ρ m α :=
  fun s => x₁ s <|> x₂ () s

/--
Fails with a recoverable error.
-/
@[always_inline, inline]
protected def failure [Alternative m] : ReaderT ρ m α :=
  fun _ => failure

instance [Alternative m] [Monad m] : Alternative (ReaderT ρ m) where
  failure := ReaderT.failure
  orElse  := ReaderT.orElse

end ReaderT

instance : MonadControl m (ReaderT ρ m) where
  stM      := id
  liftWith f ctx := f fun x => x ctx
  restoreM x _ := x

@[always_inline]
instance ReaderT.tryFinally [MonadFinally m] : MonadFinally (ReaderT ρ m) where
  tryFinally' x h ctx := tryFinally' (x ctx) (fun a? => h a? ctx)

/--
A monad with access to a read-only value of type `ρ`. The value can be locally overridden by
`withReader`, but it cannot be mutated.
-/
@[reducible] def ReaderM (ρ : Type u) := ReaderT ρ Id
