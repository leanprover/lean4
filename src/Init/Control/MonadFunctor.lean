#lang lean4
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Control.MonadLift

universes u v w

/-- A functor in the category of monads. Can be used to lift monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor). -/
class MonadFunctor (m : Type u → Type v) (n : Type u → Type w) :=
  (monadMap {α : Type u} : (∀ {β}, m β → m β) → n α → n α)

/-- The reflexive-transitive closure of `MonadFunctor`.
    `monadMap` is used to transitively lift Monad morphisms -/
class MonadFunctorT (m : Type u → Type v) (n : Type u → Type w) :=
  (monadMap {α : Type u} : (∀ {β}, m β → m β) → n α → n α)

export MonadFunctorT (monadMap)

instance (m n o) [MonadFunctorT m n] [MonadFunctor n o] : MonadFunctorT m o := {
  monadMap := fun f => MonadFunctor.monadMap (m := n) (monadMap (m := m) f)
}

instance monadFunctorRefl (m) : MonadFunctorT m m := {
  monadMap := fun f => f
}
