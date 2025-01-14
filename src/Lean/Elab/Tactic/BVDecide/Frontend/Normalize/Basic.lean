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

abbrev PreProcessM : Type → Type := ReaderT BVDecideConfig MetaM

namespace PreProcessM

def getConfig : PreProcessM BVDecideConfig := read

def run (cfg : BVDecideConfig) (x : PreProcessM α) : MetaM α :=
  ReaderT.run x cfg

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
