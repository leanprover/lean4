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

structure PreProcessState where
  /--
  Contains `FVarId` that we already know are in `bv_normalize` simp normal form and thus don't
  need to be processed again when we visit the next time.
  -/
  rewriteCache : Std.HashSet FVarId := {}

abbrev PreProcessM : Type → Type := ReaderT BVDecideConfig <| StateRefT PreProcessState MetaM

namespace PreProcessM

def getConfig : PreProcessM BVDecideConfig := read

@[inline]
def checkRewritten (fvar : FVarId) : PreProcessM Bool := do
  return (← get).rewriteCache.contains fvar

@[inline]
def rewriteFinished (fvar : FVarId) : PreProcessM Unit := do
  modify (fun s => { s with rewriteCache := s.rewriteCache.insert fvar })

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

def run (pass : Pass) (goal : MVarId) : PreProcessM (Option MVarId) := do
  withTraceNode `bv (fun _ => return m!"Running pass: {pass.name} on\n{goal}") do
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
