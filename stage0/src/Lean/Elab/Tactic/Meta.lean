/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.SyntheticMVars
import Lean.Elab.Tactic.Basic

namespace Lean.Elab
open Term

private def runTactic.defaultContext : Context := {
  fileName      := "<runTactic>"
  fileMap       := arbitrary
}

/-- Apply the give tactic code to `mvarId` in `MetaM`. -/
def runTactic (mvarId : MVarId) (tacticCode : Syntax) (ctx : Context := runTactic.defaultContext) (s : State := {}) : MetaM (List MVarId × State) := do
  modifyThe Meta.State fun s => { s with mctx := s.mctx.instantiateMVarDeclMVars mvarId }
  let go : TermElabM (List MVarId) :=
    withSynthesize (mayPostpone := false) do Tactic.run mvarId (Tactic.evalTactic tacticCode *> Tactic.pruneSolvedGoals)
  go.run ctx s

end Lean.Elab
