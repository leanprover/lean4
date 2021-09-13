/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Delta
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta

def deltaLocalDecl (declName : Name) (fvarId : FVarId) : TacticM Unit := do
  let mvarId ← getMainGoal
  let localDecl ← getLocalDecl fvarId
  let typeNew ← deltaExpand localDecl.type (. == declName)
  if typeNew == localDecl.type then
    throwTacticEx `delta mvarId m!"did not delta reduce '{declName}' at '{localDecl.userName}'"
  replaceMainGoal [← replaceLocalDeclDefEq mvarId fvarId typeNew]

def deltaTarget (declName : Name) : TacticM Unit := do
  let mvarId ← getMainGoal
  let target ← getMainTarget
  let targetNew ← deltaExpand target (. == declName)
  if targetNew == target then
    throwTacticEx `delta mvarId m!"did not delta reduce '{declName}'"
  replaceMainGoal [← replaceTargetDefEq mvarId targetNew]

/--
  "delta " ident (location)?
-/
@[builtinTactic Lean.Parser.Tactic.delta] def evalDelta : Tactic := fun stx => do
  let declName ← resolveGlobalConstNoOverload stx[1]
  let loc := expandOptLocation stx[2]
  withLocation loc (deltaLocalDecl declName) (deltaTarget declName) (throwTacticEx `delta . m!"did not delta reduce '{declName}'")

end Lean.Elab.Tactic
