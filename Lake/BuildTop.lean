/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Std.Data.RBMap

open Std
namespace Lake

/-- A recursive object fetcher. -/
def RecFetch.{u,v,w} (k : Type u) (o : Type v) (m : Type v → Type w) :=
  k → (k → m o) → m o

/-- A exception plus state monad transformer (i.e., `StateT` + `ExceptT`). -/
abbrev EStateT (ε σ m) :=
  StateT σ <| ExceptT ε m

def EStateT.run (state : σ) (self : EStateT ε σ m α) : m (Except ε (α × σ)) :=
  StateT.run self state |>.run

def EStateT.run' [Monad m] (state : σ) (self : EStateT ε σ m α) : m (Except ε α) :=
  StateT.run' self state |>.run

/--
  Monad transformer for an RBMap-based topological walk.
  If a cycle is detected, the list of keys traversed is thrown.
-/
abbrev RBTopT.{u,v} (k : Type u) (o : Type u) (cmp) (m : Type u → Type v) :=
  EStateT (List k) (RBMap k o cmp) m

/-- Auxiliary function for `buildRBTop`. -/
partial def buildRBTopCore
{k o} {cmp} {m : Type u → Type u} [BEq k] [Inhabited o] [Monad m]
(parents : List k) (fetch : RecFetch k o (RBTopT k o cmp m)) (key : k)
: RBTopT k o cmp m o := do
  -- detect cyclic builds
  if parents.contains key then
    throw <| key :: (parents.partition (· != key)).1 ++ [key]
  -- return previous output if already built
  if let some output := (← get).find? key then
    return output
  -- build the key recursively
  let output ← fetch key (buildRBTopCore (key :: parents) fetch)
  -- save the output (to prevent repeated builds of the same key)
  modify (·.insert key output)
  return output

/--
  Recursively constructs an `RBMap` of key-object pairs by
  fetching objects topologically (i.e., via a depth-first search with memoization).
  Called a suspending scheduler in "Build systems à la carte".
-/
def buildRBTop {k o} {cmp} {m} [BEq k] [Inhabited o] [Monad m]
(fetch : RecFetch k o (RBTopT k o cmp m)) (key : k) : RBTopT k o cmp m o :=
  buildRBTopCore [] fetch key
