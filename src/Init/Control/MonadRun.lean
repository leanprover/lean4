/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Leonardo de Moura
-/
prelude
import Init.Control.MonadLift

universes u v

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
(run {α : Type u} : m α → out α)

export MonadRun (run)
