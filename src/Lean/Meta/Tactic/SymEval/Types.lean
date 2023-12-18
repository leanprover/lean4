/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Types

namespace Lean.Meta.SymEval

/-!
The `seval` tactic is similar to `simp`, but it is optimized for reducing nested ground
terms, and performing partial evaluation.
-/

/--
Configuration options for `seval` tactic.
-/
-- TODO: move to `Init`
structure Config where
  maxSteps : Nat := 100000
  deriving Inhabited

structure Context where
  config         : Config := {}
  /-- `ground` is true when visiting a ground term. -/
  ground         : Bool := false
  simpTheorems   : SimpTheoremsArray := {}
  congrTheorems  : SimpCongrTheorems := {}
  dischargeDepth : Nat := 0
  deriving Inhabited

export Simp (Cache CongrCache Result)

/--
State for the `seval` tactic.
TODO: better support for hash-consing.
-/
structure State where
  cache        : Cache := {}
  congrCache   : CongrCache := {}
  numSteps     : Nat := 0

abbrev M := ReaderT Context $ StateRefT State MetaM

instance : Simp.MonadCongrCache M where
  find? f := return (← get).congrCache.find? f
  save f thm? := modify fun s => { s with congrCache := s.congrCache.insert f thm? }

def getConfig : M Config :=
  return (← read).config

def getSimpTheorems : M SimpTheoremsArray :=
  return (← read).simpTheorems

def getSimpCongrTheorems : M SimpCongrTheorems :=
  return (← read).congrTheorems

end Lean.Meta.SymEval
