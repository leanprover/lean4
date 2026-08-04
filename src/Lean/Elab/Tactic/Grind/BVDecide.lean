/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Tactic.BVDecide.Main
import Lean.Elab.Tactic.BVDecide.BVTrace
import Lean.Meta.Tactic.BVDecide.Normalize

/-!
This module provides the implementation of the `bv_decide` family of tactics in `sym =>` mode.
-/

namespace Lean.Elab.Tactic.Grind

def elabBVDecideConfig (cfg : TSyntax `Lean.Parser.Tactic.optConfig) (goal : MVarId)
    (elaborator : Name) : TermElabM BVDecide.BVDecideConfig := do
  Meta.Tactic.BVDecide.elabBVDecideConfig cfg
    |>.run { elaborator }
    |>.run' { goals := [goal] }

open Meta.Tactic.BVDecide

@[builtin_grind_tactic Parser.Tactic.Grind.bvDecide] def evalBvDecide : GrindTactic
  | `(grind| bv_decide $cfg:optConfig) => do
    ensureSym
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfg g.mvarId `bv_decide
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile cfg
      discard <| liftSymM <| bvDecide g.mvarId cfg
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic Parser.Tactic.Grind.bvTrace] def evalBvTrace : GrindTactic
  | `(grind| bv_decide?%$tk $cfgStx:optConfig) => do
    ensureSym
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfgStx g.mvarId `bv_decide?
    let ctx ← BVDecide.BVTrace.mkContext cfg
    match ← liftSymM <| BVDecide.BVTrace.evalBvTrace g.mvarId ctx with
    | .normalize =>
      let normalizeStx ← `(grind| bv_normalize $cfgStx:optConfig)
      Meta.Tactic.TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
    | .check lratFile =>
      let bvCheckStx ← `(grind| bv_check $cfgStx:optConfig $(quote lratFile.toString))
      Meta.Tactic.TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic Parser.Tactic.Grind.bvCheck] def evalBvCheck : GrindTactic
  | `(grind| bv_check%$tk $cfgStx:optConfig $path:str) => do
    ensureSym
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfgStx g.mvarId `bv_check
    let ctx ← BVDecide.BVCheck.mkContext path.getString cfg
    liftSymM <| BVDecide.BVCheck.evalBvCheck g.mvarId ctx do
      let bvNormalizeStx ← `(grind| bv_normalize $cfgStx)
      logWarning m!"This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."
      Meta.Tactic.TryThis.addSuggestion tk bvNormalizeStx (origSpan? := ← getRef)
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic Parser.Tactic.Grind.bvNormalize]
def evalBVNormalize : GrindTactic := fun
  | `(grind| bv_normalize $cfg:optConfig) => do
    ensureSym
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfg g.mvarId `bv_normalize
    let (_, state) ← liftSymM <| Meta.Tactic.BVDecide.Normalize.bvNormalize.run cfg g.mvarId
    if ← state.goal.isAssigned then
      replaceMainGoal []
    else
      throwError "`bv_normalize` failed to close the goal"
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Grind
