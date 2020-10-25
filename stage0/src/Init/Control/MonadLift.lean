/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich

Classy functions for lifting monadic actions of different shapes.

This theory is roughly modeled after the Haskell 'layers' package https://hackage.haskell.org/package/layers-0.1.
Please see https://hackage.haskell.org/package/layers-0.1/docs/Documentation-Layers-Overview.html for an exhaustive discussion of the different approaches to lift functions.
-/
prelude
import Init.Control.Monad
import Init.Coe

universes u v w

/-- A Function for lifting a computation from an inner Monad to an outer Monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class MonadLift (m : Type u → Type v) (n : Type u → Type w) :=
  (monadLift : {α : Type u} → m α → n α)

/-- The reflexive-transitive closure of `MonadLift`.
    `monadLift` is used to transitively lift monadic computations such as `StateT.get` or `StateT.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class MonadLiftT (m : Type u → Type v) (n : Type u → Type w) :=
  (monadLift : {α : Type u} → m α → n α)

export MonadLiftT (monadLift)

abbrev liftM := @monadLift

@[inline] def liftCoeM {m : Type u → Type v} {n : Type u → Type w} {α β : Type u} [MonadLiftT m n] [∀ a, CoeT α a β] [Monad n] (x : m α) : n β := do
  let a ← liftM x
  pure (coe a)

instance (m n o) [MonadLiftT m n] [MonadLift n o] : MonadLiftT m o := {
  monadLift := fun x => MonadLift.monadLift (m := n) (monadLift x)
}

instance (m) : MonadLiftT m m := {
  monadLift := fun x => x
}
