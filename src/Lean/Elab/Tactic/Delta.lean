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

def deltaLocalDecl (declNames : Array Name) (fvarId : FVarId) : TacticM Unit := do
  let mvarId ← getMainGoal
  let localDecl ← fvarId.getDecl
  let typeNew ← deltaExpand localDecl.type declNames.contains
  if typeNew == localDecl.type then
    throwTacticEx `delta mvarId m!"did not delta reduce {declNames} at {localDecl.userName}"
  replaceMainGoal [← mvarId.replaceLocalDeclDefEq fvarId typeNew]

def deltaTarget (declNames : Array Name) : TacticM Unit := do
  let mvarId ← getMainGoal
  let target ← getMainTarget
  let targetNew ← deltaExpand target declNames.contains
  if targetNew == target then
    throwTacticEx `delta mvarId m!"did not delta reduce {declNames}"
  replaceMainGoal [← mvarId.replaceTargetDefEq targetNew]

/-- "delta " ident+ (location)? -/
@[builtin_tactic Lean.Parser.Tactic.delta] def evalDelta : Tactic := fun stx => do
  let declNames ← stx[1].getArgs.mapM resolveGlobalConstNoOverloadWithInfo
  let loc := expandOptLocation stx[2]
  withLocation loc (deltaLocalDecl declNames) (deltaTarget declNames)
    (throwTacticEx `delta · m!"did not delta reduce {declNames}")

end Lean.Elab.Tactic
