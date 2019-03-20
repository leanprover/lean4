/-
Copyright (c) 2016 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich

Classy functions for lifting monadic actions of different shapes.

This theory is roughly modeled after the Haskell 'layers' package https://hackage.haskell.org/package/layers-0.1.
Please see https://hackage.haskell.org/package/layers-0.1/docs/Documentation-Layers-Overview.html for an exhaustive discussion of the different approaches to lift functions.
-/
prelude
import init.Function init.coe
import init.control.Monad

universes u v w

/-- A Function for lifting a computation from an inner Monad to an outer Monad.
    Like [MonadTrans](https://hackage.haskell.org/package/transformers-0.5.5.0/docs/Control-Monad-Trans-Class.html),
    but `n` does not have to be a monad transformer.
    Alternatively, an implementation of [MonadLayer](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLayer) without `layerInvmap` (so far). -/
class HasMonadLift (m : Type u → Type v) (n : Type u → Type w) :=
(monadLift {} : ∀ {α}, m α → n α)

/-- The reflexive-transitive closure of `HasMonadLift`.
    `monadLift` is used to transitively lift monadic computations such as `StateT.get` or `StateT.put s`.
    Corresponds to [MonadLift](https://hackage.haskell.org/package/layers-0.1/docs/Control-Monad-Layer.html#t:MonadLift). -/
class HasMonadLiftT (m : Type u → Type v) (n : Type u → Type w) :=
(monadLift {} : ∀ {α}, m α → n α)

export HasMonadLiftT (monadLift)

/-- A coercion that may reduce the need for explicit lifting.
    Because of [limitations of the current coercion resolution](https://github.com/leanprover/Lean/issues/1402), this definition is not marked as a global instance and should be marked locally instead. -/
@[reducible] def hasMonadLiftToHasCoe {m n} [HasMonadLiftT m n] {α} : HasCoe (m α) (n α) :=
⟨monadLift⟩

instance hasMonadLiftTTrans (m n o) [HasMonadLift n o] [HasMonadLiftT m n] : HasMonadLiftT m o :=
⟨λ α ma, HasMonadLift.monadLift (monadLift ma : n α)⟩

instance hasMonadLiftTRefl (m) : HasMonadLiftT m m :=
⟨λ α, id⟩

lemma monadLiftRefl {m : Type u → Type v} {α} : (monadLift : m α → m α) = id := rfl


/-- A Functor in the control of monads. Can be used to lift Monad-transforming functions.
    Based on pipes' [MFunctor](https://hackage.haskell.org/package/pipes-2.4.0/docs/Control-MFunctor.html),
    but not restricted to monad transformers.
    Alternatively, an implementation of [MonadTransFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadTransFunctor).


    Remark: other libraries equate `m` and `m'`, and `n` and `n'`. We need to distinguish them to be able to implement
    gadgets such as `MonadStateAdapter` and `MonadReaderAdapter`. -/
class MonadFunctor (m m' : Type u → Type v) (n n' : Type u → Type w) :=
(monadMap {} {α : Type u} : (∀ {β}, m β → m' β) → n α → n' α)

/-- The reflexive-transitive closure of `MonadFunctor`.
    `monadMap` is used to transitively lift Monad morphisms such as `StateT.zoom`.
    A generalization of [MonadLiftFunctor](http://duairc.netsoc.ie/layers-docs/Control-Monad-Layer.html#t:MonadLiftFunctor), which can only lift endomorphisms (i.e. m = m', n = n'). -/
class MonadFunctorT (m m' : Type u → Type v) (n n' : Type u → Type w) :=
(monadMap {} {α : Type u} : (∀ {β}, m β → m' β) → n α → n' α)

export MonadFunctorT (monadMap)

instance monadFunctorTTrans (m m' n n' o o') [MonadFunctor n n' o o'] [MonadFunctorT m m' n n'] :
  MonadFunctorT m m' o o' :=
⟨λ α f, MonadFunctor.monadMap (λ β, (monadMap @f : n β → n' β))⟩

instance monadFunctorTRefl (m m') : MonadFunctorT m m' m m' :=
⟨λ α f, f⟩

lemma monadMapRefl {m m' : Type u → Type v} (f : ∀ {β}, m β → m' β) {α} : (monadMap @f : m α → m' α) = f := rfl

/-- Run a Monad stack to completion.
    `run` should be the composition of the transformers' individual `run` functions.
    This class mostly saves some typing when using highly nested Monad stacks:
    ```
    @[reducible] def MyMonad := ReaderT myCfg $ StateT myState $ ExceptT myErr id
    -- def MyMonad.run {α : Type} (x : MyMonad α) (cfg : myCfg) (st : myState) := ((x.run cfg).run st).run
    def MyMonad.run {α : Type} (x : MyMonad α) := MonadRun.run x
    ```
    -/
class MonadRun (out : outParam $ Type u → Type v) (m : Type u → Type v) :=
(run {} {α : Type u} : m α → out α)

export MonadRun (run)
