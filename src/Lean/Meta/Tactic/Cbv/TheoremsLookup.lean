/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Match.MatchEqsExt
import Lean.Elab.PreDefinition.EqUnfold
import Lean.Meta.Eqns


namespace Lean.Meta.Sym.Simp

def Theorems.insertMany (thms : Theorems) (toInsert : Array Theorem) : Theorems :=
  Array.foldl Theorems.insert thms toInsert

end Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

/--
Get or create cached Theorems for function equations.
Retrieves equations via `getEqnsFor?` and caches the resulting Theorems object.
-/
public structure CbvTheoremsLookupState where
  eqnTheorems : PHashMap Name Theorems := {}
  unfoldTheorems : PHashMap Name Theorem := {}
  matchTheorems : PHashMap Name Theorems := {}
  deriving Inhabited

builtin_initialize cbvTheoremsLookup : EnvExtension CbvTheoremsLookupState ←
  registerEnvExtension (pure {}) (asyncMode := .local)

public def getEqnTheorems (fnName : Name) : MetaM Theorems := do
  let env ← getEnv
  let cache := cbvTheoremsLookup.getState env
  if let some thms := cache.eqnTheorems.find? fnName then
    return thms
  else
    -- Compute theorems from equation names
    let some eqnNames ← getEqnsFor? fnName | return {}
    let thms := Theorems.insertMany {} <| ← eqnNames.mapM mkTheoremFromDecl
    -- Store in cache
    modifyEnv fun env =>
      cbvTheoremsLookup.modifyState env fun cache =>
        { cache with eqnTheorems := cache.eqnTheorems.insert fnName thms }
    return thms

public def getUnfoldTheorem (fnName : Name) : MetaM (Option Theorem) := do
  let env ← getEnv
  let cache := cbvTheoremsLookup.getState env
  if let some thm := cache.unfoldTheorems.find? fnName then
    return some thm
  else
    let some unfoldEqn ← getConstUnfoldEqnFor? fnName | return none
    let thm ← mkTheoremFromDecl unfoldEqn

    modifyEnv fun env =>
      cbvTheoremsLookup.modifyState env fun cache =>
        { cache with unfoldTheorems := cache.unfoldTheorems.insert fnName thm }
    return some thm

public def getMatchTheorems (matcherName : Name) : MetaM Theorems := do
  let env ← getEnv
  let cache := cbvTheoremsLookup.getState env
  if let some thms := cache.matchTheorems.find? matcherName then
    return thms
  else
    let eqns ← Match.getEquationsFor matcherName
    let thms := Theorems.insertMany {} <| ← eqns.eqnNames.mapM mkTheoremFromDecl

    modifyEnv fun env =>
      cbvTheoremsLookup.modifyState env fun cache =>
        { cache with matchTheorems := cache.matchTheorems.insert matcherName thms }
    return thms

end Lean.Meta.Tactic.Cbv
