/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Store
import Lake.Util.EquipT

/-!
# Topological / Suspending Recursive Builder

This module defines a recursive build function that topologically
(ι.e., via a depth-first search with memoization) builds the elements of
a build store.

This is called a suspending scheduler in *Build systems à la carte*.
-/

open Std
namespace Lake

/-! ## Abstractions -/

/-- A dependently typed object builder. -/
abbrev DBuildFn.{u,v,w} (ι : Type u) (β : ι → Type v) (m : Type v → Type w) :=
  (i : ι) → m (β i)

/-- A dependently typed recursive object builder. -/
abbrev DRecBuildFn.{u,v,w} (ι : Type u) (β : ι → Type v) (m : Type v → Type w) :=
  (i : ι) → EquipT (DBuildFn ι β m)  m (β i)

/-- A recursive object builder. -/
abbrev RecBuildFn ι α m := DRecBuildFn ι (fun _ => α) m

/-- `ExceptT` for build cycles. -/
abbrev CycleT (κ) :=
  ExceptT (List κ)

/-! ## Algorithm -/

/-- Auxiliary function for `buildTop`. -/
@[specialize] partial def buildTopCore [BEq κ] [Monad m] [MonadDStore κ β m]
(parents : List κ) (keyOf : ι → κ) (build : DRecBuildFn ι (β ∘ keyOf) (CycleT κ m))
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
(keyOf : ι → κ) (build : DRecBuildFn ι (β ∘ keyOf) (CycleT κ m))
(info : ι) : CycleT κ m (β (keyOf info)) :=
  buildTopCore [] keyOf build info

/--
Recursively fills a `MonadStore` of key-object pairs by
building objects topologically (ι.e., via a depth-first search with memoization).
If a cycle is detected, the list of keys traversed is thrown.
-/
@[inline] def buildTop [BEq κ] [Monad m] [MonadStore κ α m]
(keyOf : ι → κ) (build : RecBuildFn ι α (CycleT κ m)) (info : ι) : CycleT κ m α :=
  buildDTop (fun _ => α) keyOf build info
