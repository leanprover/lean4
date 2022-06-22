/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lake.Util.DRBMap

open Std
namespace Lake

--------------------------------------------------------------------------------
-- # Build Store
--------------------------------------------------------------------------------

/-- A monad equipped with a dependently typed key-value store for a particular key. -/
class MonadStore1 {κ : Type u} (k : κ) (α : outParam $ Type v) (m : Type v → Type w) where
  fetch? : m (Option α)
  store : α → m PUnit

export MonadStore1 (fetch? store)

/-- A monad equipped with a dependently typed key-object store. -/
class MonadDStore (κ : Type u) (β : outParam $ κ → Type v) (m : Type v → Type w) where
  fetch? : (key : κ) → m (Option (β key))
  store : (key : κ) → β key → m PUnit

instance [MonadDStore κ β m] : MonadStore1 k (β k) m where
  fetch? := MonadDStore.fetch? k
  store o := MonadDStore.store k o

/-- A monad equipped with a key-object store. -/
abbrev MonadStore κ α m := MonadDStore κ (fun _ => α) m

instance [MonadLiftT m n] [MonadDStore κ β m] : MonadDStore κ β n where
  fetch? k := liftM (m := m) <| fetch? k
  store k a := liftM (m := m) <| store k a

instance [Monad m] [EqOfCmpWrt κ β cmp] : MonadDStore κ β (StateT (DRBMap κ β cmp) m) where
  fetch? k := return (← get).find? k
  store k a :=  modify (·.insert k a)

instance [Monad m] : MonadStore κ α (StateT (RBMap κ α cmp) m) where
  fetch? k := return (← get).find? k
  store k a := modify (·.insert k a)

--------------------------------------------------------------------------------
-- # Topological / Suspending Builder
--------------------------------------------------------------------------------

-- ## Abstractions

/-- A dependently typed object builder. -/
abbrev DBuild.{u,v,w} (ι : Type u) (β : ι → Type v) (m : Type v → Type w) :=
  (i : ι) → m (β i)

/-- A dependently typed recursive object builder. -/
abbrev DRecBuild.{u,v,w} (ι : Type u) (β : ι → Type v) (m : Type v → Type w) :=
  (i : ι) → DBuild ι β m → m (β i)

/-- A recursive object builder. -/
abbrev RecBuild ι α m := DRecBuild ι (fun _ => α) m

/-- `ExceptT` for build cycles. -/
abbrev CycleT (κ) :=
  ExceptT (List κ)

-- ## Algorithm

/-- Auxiliary function for `buildTop`. -/
@[specialize] partial def buildTopCore [BEq κ] [Monad m] [MonadDStore κ β m]
(parents : List κ) (keyOf : ι → κ) (build : DRecBuild ι (β ∘ keyOf) (CycleT κ m))
(info : ι) : CycleT κ m (β (keyOf info)) := do
  let key := keyOf info
  -- return previous output if already built
  if let some output ← fetch? key then
    return output
  -- detect cyclic builds
  if parents.contains key then
    throw <| key :: (parents.partition (· != key)).1 ++ [key]
  -- build the key recursively
  let output ← build info <| buildTopCore (key :: parents) keyOf build
  -- save the output (to prevent repeated builds of the same key)
  store key output
  return output

/-- Dependently typed version of `buildTop`. -/
@[inline] def buildDTop (β) [BEq κ] [Monad m] [MonadDStore κ β m]
(keyOf : ι → κ) (build : DRecBuild ι (β ∘ keyOf) (CycleT κ m))
(info : ι) : CycleT κ m (β (keyOf info)) :=
  buildTopCore [] keyOf build info

/--
Recursively fills a `MonadStore` of key-object pairs by
building objects topologically (ι.e., via a depth-first search with memoization).
If a cycle is detected, the list of keys traversed is thrown.

Called a suspending scheduler in "Build systems à la carte".
-/
@[inline] def buildTop [BEq κ] [Monad m] [MonadStore κ α m]
(keyOf : ι → κ) (build : RecBuild ι α (CycleT κ m)) (info : ι) : CycleT κ m α :=
  buildDTop (fun _ => α) keyOf build info
