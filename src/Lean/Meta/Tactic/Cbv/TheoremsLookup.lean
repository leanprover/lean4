/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/

module

prelude
public import Lean.Meta.Tactic.Cbv.Types
import Lean.Meta.Match.MatchEqsExt
import Lean.Meta.Eqns


namespace Lean.Meta.Sym.Simp

def Theorems.insertMany (thms : Theorems) (toInsert : Array Theorem) : Theorems :=
  Array.foldl Theorems.insert thms toInsert

end Lean.Meta.Sym.Simp

namespace Lean.Meta.Tactic.Cbv
open Lean.Meta.Sym.Simp

builtin_initialize cbvTheoremsLookup : EnvExtension CbvTheoremsLookupState ←
  registerEnvExtension (pure {}) (asyncMode := .local)

/--
Get or create cached Theorems for function equations.
Retrieves equations via `getEqnsFor?` and caches the resulting Theorems object.
-/
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

/--
Get or create cached Theorem for unfold equation.
Retrieves unfold equation via `getUnfoldEqnFor?` and caches the resulting Theorem.
-/
public def getUnfoldTheorem (fnName : Name) : MetaM (Option Theorem) := do
  let env ← getEnv
  let cache := cbvTheoremsLookup.getState env
  if let some thm := cache.unfoldTheorems.find? fnName then
    return some thm
  else
    -- Compute theorem from unfold equation
    let some unfoldEqn ← getUnfoldEqnFor? fnName (nonRec := true) | return none
    let thm ← mkTheoremFromDecl unfoldEqn
    -- Store in cache
    modifyEnv fun env =>
      cbvTheoremsLookup.modifyState env fun cache =>
        { cache with unfoldTheorems := cache.unfoldTheorems.insert fnName thm }
    return some thm

/--
Get or create cached Theorems for match equations.
Retrieves match equations via `Match.getEquationsFor` and caches the resulting Theorems object.
-/
public def getMatchTheorems (matcherName : Name) : MetaM Theorems := do
  let env ← getEnv
  let cache := cbvTheoremsLookup.getState env
  if let some thms := cache.matchTheorems.find? matcherName then
    return thms
  else
    -- Compute theorems from match equation names
    let eqns ← Match.getEquationsFor matcherName
    let thms := Theorems.insertMany {} <| ← eqns.eqnNames.mapM mkTheoremFromDecl
    -- Store in cache
    modifyEnv fun env =>
      cbvTheoremsLookup.modifyState env fun cache =>
        { cache with matchTheorems := cache.matchTheorems.insert matcherName thms }
    return thms

end Lean.Meta.Tactic.Cbv
