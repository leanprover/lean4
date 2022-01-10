/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Unfold
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location

namespace Lean.Elab.Tactic
open Meta

def unfoldLocalDecl (declName : Name) (fvarId : FVarId) : TacticM Unit := do
  replaceMainGoal [← Meta.unfoldLocalDecl (← getMainGoal) fvarId declName]

def unfoldTarget (declName : Name) : TacticM Unit := do
  replaceMainGoal [← Meta.unfoldTarget (← getMainGoal) declName]

/--
  "unfold " ident (location)?
-/
@[builtinTactic Lean.Parser.Tactic.unfold] def evalUnfold : Tactic := fun stx => do
  let declName ← resolveGlobalConstNoOverload stx[1]
  let loc := expandOptLocation stx[2]
  withLocation loc (unfoldLocalDecl declName) (unfoldTarget declName) (throwTacticEx `unfold . m!"did not unfold '{declName}'")

end Lean.Elab.Tactic
