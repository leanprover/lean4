/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Std.Data.RBMap

open Std
namespace Lake

--------------------------------------------------------------------------------
-- # Topological / Suspending Builder
--------------------------------------------------------------------------------

-- ## Abstractions

/-- A recursive object builder. -/
def RecBuild.{u,v,w} (i : Type u) (o : Type v) (m : Type v → Type w) :=
  i → (i → m o) → m o

/-- A monad equipped with a key-object store. -/
class MonadStore (k : Type u) (o : Type v) (m : Type v → Type w) where
  fetch? : k → m (Option o)
  store : k → o → m PUnit

export MonadStore (fetch? store)

instance [Monad m] [MonadStore k o m] : MonadStore k o (ExceptT ε m) where
  fetch? key := liftM (m := m) <| fetch? key
  store key obj := liftM (m := m) <| store key obj

-- ## Algorithm

/-- Auxiliary function for `buildTop`. -/
partial def buildTopCore [BEq k] [Inhabited o] [Monad m] [MonadStore k o m]
(parents : List k) (build : RecBuild i o (ExceptT (List k) m)) (keyOf : i → k) (info : i) : ExceptT (List k) m o := do
  let key := keyOf info
  -- detect cyclic builds
  if parents.contains key then
    throw <| key :: (parents.partition (· != key)).1 ++ [key]
  -- return previous output if already built
  if let some output ← fetch? key then
    return output
  -- build the key recursively
  let output ← build info <| buildTopCore (key :: parents) build keyOf
  -- save the output (to prevent repeated builds of the same key)
  store key output
  return output

/--
  Recursively fills a `MonadStore` of key-object pairs by
  building objects topologically (i.e., via a depth-first search with memoization).
  Called a suspending scheduler in "Build systems à la carte".
-/
def buildTop [BEq k] [Inhabited o] [Monad m] [MonadStore k o m]
(build : RecBuild i o (ExceptT (List k) m)) (keyOf : i → k) (info : i) : ExceptT (List k) m o :=
  buildTopCore [] build keyOf info

--------------------------------------------------------------------------------
-- # RBMap Version
--------------------------------------------------------------------------------

/-- A exception plus state monad transformer (i.e., `ExceptT` + `StateT`). -/
abbrev EStateT (ε σ m) :=
  ExceptT ε <| StateT σ m

def EStateT.run (state : σ) (self : EStateT ε σ m α) : m (Except ε α × σ) :=
  ExceptT.run self |>.run state

def EStateT.run' [Monad m] (state : σ) (self : EStateT ε σ m α) : m (Except ε α) :=
  ExceptT.run self |>.run' state

/-- A transformer that adds an `RBMap` store to a monad. -/
abbrev RBMapT.{u,v} (k : Type u) (o : Type u) (cmp) (m : Type u → Type v) :=
  StateT (RBMap k o cmp) m

instance (cmp) [Monad m] : MonadStore k o (RBMapT k o cmp m) where
  fetch? key := do (← get).find? key
  store key obj := modify (·.insert key obj)

/--
  Monad transformer for an RBMap-based topological walk.
  If a cycle is detected, the list of keys traversed is thrown.
-/
abbrev RBTopT.{u,v} (k : Type u) (o : Type u) (cmp) (m : Type u → Type v) :=
  EStateT (List k) (RBMap k o cmp) m

/-- The `RBMap` version of `buildTop`. -/
def buildRBTop {k o} {cmp} {m} [BEq k] [Inhabited o] [Monad m]
(build : RecBuild i o (RBTopT k o cmp m)) (keyOf : i → k) (info : i) : RBTopT k o cmp m o :=
  buildTop build keyOf info
