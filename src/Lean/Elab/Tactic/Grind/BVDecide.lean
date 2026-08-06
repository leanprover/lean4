/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
import Lean.Elab.Tactic.Grind.Basic
import Lean.Meta.Tactic.BVDecide.Main
import Lean.Elab.Tactic.BVDecide
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
  | `(grind| bv_decide $cfg:optConfig $[$types:bvTypes]?) => do
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfg g.mvarId `bv_decide
    let types ← elabBVDecideTypes types
    IO.FS.withTempFile fun _ lratFile => do
      let cfg ← TacticContext.new lratFile cfg types
      discard <| liftGrindM <| bvDecide (.grindTarget g) cfg
      replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic Parser.Tactic.Grind.bvTrace] def evalBvTrace : GrindTactic
  | `(grind| bv_decide?%$tk $cfgStx:optConfig $[$typesStx:bvTypes]?) => do
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfgStx g.mvarId `bv_decide?
    let types ← elabBVDecideTypes typesStx
    let ctx ← BVDecide.BVTrace.mkContext cfg types
    match ← liftGrindM <| BVDecide.BVTrace.evalBvTrace (.grindTarget g) ctx with
    | .normalize =>
      let normalizeStx ← `(grind| bv_normalize $cfgStx:optConfig $[$typesStx:bvTypes]?)
      Meta.Tactic.TryThis.addSuggestion tk normalizeStx (origSpan? := ← getRef)
    | .check lratFile =>
      let bvCheckStx ←
        `(grind| bv_check $cfgStx:optConfig $[$typesStx:bvTypes]? $(quote lratFile.toString))
      Meta.Tactic.TryThis.addSuggestion tk bvCheckStx (origSpan? := ← getRef)
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic Parser.Tactic.Grind.bvCheck] def evalBvCheck : GrindTactic
  | `(grind| bv_check%$tk $cfgStx:optConfig $[$typesStx:bvTypes]? $path:str) => do
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfgStx g.mvarId `bv_check
    let types ← elabBVDecideTypes typesStx
    let ctx ← BVDecide.BVCheck.mkContext path.getString cfg types
    liftGrindM <| BVDecide.BVCheck.evalBvCheck (.grindTarget g) ctx do
      let bvNormalizeStx ← `(grind| bv_normalize $cfgStx $[$typesStx:bvTypes]?)
      logWarning m!"This goal can be closed by only applying bv_normalize, no need to keep the LRAT proof around."
      Meta.Tactic.TryThis.addSuggestion tk bvNormalizeStx (origSpan? := ← getRef)
    replaceMainGoal []
  | _ => throwUnsupportedSyntax

@[builtin_grind_tactic Parser.Tactic.Grind.bvNormalize]
def evalBVNormalize : GrindTactic := fun
  | `(grind| bv_normalize $cfg:optConfig $[$types:bvTypes]?) => do
    BVDecide.ensureBvDecide
    let g ← getMainGoal
    let cfg ← elabBVDecideConfig cfg g.mvarId `bv_normalize
    let types ← elabBVDecideTypes types
    let (_, state) ← liftGrindM <|
      Meta.Tactic.BVDecide.Normalize.bvNormalize.run { config := cfg, restrictedTypes := types } (.grindTarget g)
    if ← state.target.mvarId.isAssigned then
      replaceMainGoal []
    else
      throwError "`bv_normalize` failed to close the goal"
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Grind
