/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Lean.Meta.Basic
import Lean.Elab.Tactic.BVDecide.Frontend.Attr

/-!
This module contains the basic preprocessing pipeline framework for `bv_normalize`.
-/

namespace Lean.Elab.Tactic.BVDecide
namespace Frontend.Normalize

open Lean.Meta

-- TODO(henrik): Add further match statements like matches with default cases
/--
The various kinds of matches supported by the match to cond infrastructure.
-/
inductive MatchKind
  /--
  It is a full match statement on an enum inductive with one constructor handled per arm.
  -/
  | simpleEnum (info : InductiveVal)

/--
Contains the result of the type analysis to be used in the structures and enums pass.
-/
structure TypeAnalysis where
  /--
  Structures that are interesting for the structures pass.
  -/
  interestingStructures : Std.HashSet Name := {}
  /--
  Inductives enums that are interesting for the enums pass.
  -/
  interestingEnums : Std.HashSet Name := {}
  /--
  `func.match_x` auxiliary declarations that we consider interesting.
  -/
  interestingMatchers : Std.HashMap Name MatchKind := {}
  /--
  Other types that we've seen that are not interesting, currently only used as a cache.
  -/
  uninteresting : Std.HashSet Name := {}

structure PreProcessState where
  /--
  Contains `FVarId` that we already know are in `bv_normalize` simp normal form and thus don't
  need to be processed again when we visit the next time.
  -/
  rewriteCache : Std.HashSet FVarId := {}
  /--
  Analysis results for the structure and enum pass if required.
  -/
  typeAnalysis : TypeAnalysis := {}

abbrev PreProcessM : Type → Type := ReaderT BVDecideConfig <| StateRefT PreProcessState MetaM

namespace PreProcessM

@[inline]
def getConfig : PreProcessM BVDecideConfig := read

@[inline]
def checkRewritten (fvar : FVarId) : PreProcessM Bool := do
  return (← get).rewriteCache.contains fvar

@[inline]
def rewriteFinished (fvar : FVarId) : PreProcessM Unit := do
  modify (fun s => { s with rewriteCache := s.rewriteCache.insert fvar })

@[inline]
def getTypeAnalysis : PreProcessM TypeAnalysis := do
  return (← get).typeAnalysis

@[inline]
def lookupInterestingStructure (n : Name) : PreProcessM (Option Bool) := do
  let s ← getTypeAnalysis
  if s.uninteresting.contains n then
    return some false
  else if s.interestingStructures.contains n then
    return some true
  else
    return none

@[inline]
def modifyTypeAnalysis (f : TypeAnalysis → TypeAnalysis) :
    PreProcessM Unit := do
  modify fun s => { s with typeAnalysis := f s.typeAnalysis }

@[inline]
def markInterestingStructure (n : Name) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with interestingStructures := s.interestingStructures.insert n })

@[inline]
def markInterestingEnum (n : Name) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with interestingEnums := s.interestingEnums.insert n })

@[inline]
def markInterestingMatcher (n : Name) (k : MatchKind) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with interestingMatchers := s.interestingMatchers.insert n k })

@[inline]
def markUninterestingConst (n : Name) : PreProcessM Unit := do
  modifyTypeAnalysis (fun s => { s with uninteresting := s.uninteresting.insert n })

@[inline]
def run (cfg : BVDecideConfig) (goal : MVarId) (x : PreProcessM α) : MetaM α := do
  let hyps ← goal.withContext do getPropHyps
  ReaderT.run x cfg |>.run' { rewriteCache := Std.HashSet.empty hyps.size }

end PreProcessM

/--
A pass in the normalization pipeline. Takes the current goal and produces a refined one or closes
the goal fully, indicated by returning `none`.
-/
structure Pass where
  name : Name
  run' : MVarId → PreProcessM (Option MVarId)

namespace Pass

@[inline]
def run (pass : Pass) (goal : MVarId) : PreProcessM (Option MVarId) := do
  withTraceNode `Meta.Tactic.bv (fun _ => return m!"Running pass: {pass.name} on\n{goal}") do
    pass.run' goal

/--
Repeatedly run a list of `Pass` until they either close the goal or an iteration doesn't change
the goal anymore.
-/
partial def fixpointPipeline (passes : List Pass) (goal : MVarId) : PreProcessM (Option MVarId) := do
  let mut newGoal := goal
  for pass in passes do
    if let some nextGoal ← pass.run newGoal then
      newGoal := nextGoal
    else
      trace[Meta.Tactic.bv] "Fixpoint iteration solved the goal"
      return none

  if goal != newGoal then
    trace[Meta.Tactic.bv] m!"Rerunning pipeline on:\n{newGoal}"
    fixpointPipeline passes newGoal
  else
    trace[Meta.Tactic.bv] "Pipeline reached a fixpoint"
    return newGoal

end Pass

end Frontend.Normalize
end Lean.Elab.Tactic.BVDecide
