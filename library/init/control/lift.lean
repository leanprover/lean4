/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich

Classy functions for lifting monadic actions of different shapes.

This theory is roughly modeled after the Haskell 'layers' package https://hackage.haskell.org/package/layers-0.1.
Please see https://hackage.haskell.org/package/layers-0.1/docs/Documentation-Layers-Overview.html for an exhaustive discussion of the different approaches to lift functions.
-/
prelude
import init.function init.coe
import init.control.monad

universes u v w

/-- A function for lifting a computation from an inner monad to an outer monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class hasMonadLift (m : Type u → Type v) (n : Type u → Type w) :=
(monadLift {} : ∀ {α}, m α → n α)

/-- The reflexive-transitive closure of `hasMonadLift`.
    `monadLift` is used to transitively lift monadic computations such as `stateT.get` or `stateT.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class hasMonadLiftT (m : Type u → Type v) (n : Type u → Type w) :=
(monadLift {} : ∀ {α}, m α → n α)

export hasMonadLiftT (monadLift)

/-- A coercion that may reduce the need for explicit lifting.
    Because of [limitations of the current coercion resolution](https://github.com/leanprover/lean/issues/1402), this definition is not marked as a global instance and should be marked locally instead. -/
@[reducible] def hasMonadLiftToHasCoe {m n} [hasMonadLiftT m n] {α} : hasCoe (m α) (n α) :=
⟨monadLift⟩

instance hasMonadLiftTTrans (m n o) [hasMonadLift n o] [hasMonadLiftT m n] : hasMonadLiftT m o :=
⟨λ α ma, hasMonadLift.monadLift (monadLift ma : n α)⟩

instance hasMonadLiftTRefl (m) : hasMonadLiftT m m :=
⟨λ α, id⟩

lemma monadLiftRefl {m : Type u → Type v} {α} : (monadLift : m α → m α) = id := rfl


/-- A functor in the control of monads. Can be used to lift monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor).


    Remark: other libraries equate `m` and `m'`, and `n` and `n'`. We need to distinguish them to be able to implement
    gadgets such as `monadStateAdapter` and `monadReaderAdapter`. -/
class monadFunctor (m m' : Type u → Type v) (n n' : Type u → Type w) :=
(monadMap {} {α : Type u} : (∀ {β}, m β → m' β) → n α → n' α)

/-- The reflexive-transitive closure of `monadFunctor`.
    `monadMap` is used to transitively lift monad morphisms such as `stateT.zoom`.
    A generalization of [MonadLiftFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadLiftFunctor), which can only lift endomorphisms (i.e. m = m', n = n'). -/
class monadFunctorT (m m' : Type u → Type v) (n n' : Type u → Type w) :=
(monadMap {} {α : Type u} : (∀ {β}, m β → m' β) → n α → n' α)

export monadFunctorT (monadMap)

instance monadFunctorTTrans (m m' n n' o o') [monadFunctor n n' o o'] [monadFunctorT m m' n n'] :
  monadFunctorT m m' o o' :=
⟨λ α f, monadFunctor.monadMap (λ β, (monadMap @f : n β → n' β))⟩

instance monadFunctorTRefl (m m') : monadFunctorT m m' m m' :=
⟨λ α f, f⟩

lemma monadMapRefl {m m' : Type u → Type v} (f : ∀ {β}, m β → m' β) {α} : (monadMap @f : m α → m' α) = f := rfl

/-- Run a monad stack to completion.
    `run` should be the composition of the transformers' individual `run` functions.
    This class mostly saves some typing when using highly nested monad stacks:
    ```
    @[reducible] def myMonad := readerT myCfg $ stateT myState $ exceptT myErr id
    -- def myMonad.run {α : Type} (x : myMonad α) (cfg : myCfg) (st : myState) := ((x.run cfg).run st).run
    def myMonad.run {α : Type} (x : myMonad α) := monadRun.run x
    ```
    -/
class monadRun (out : outParam $ Type u → Type v) (m : Type u → Type v) :=
(run {} {α : Type u} : m α → out α)

export monadRun (run)
