/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mac Malone
-/
import Lean.Elab.Term
import Lean.Elab.SyntheticMVars
import Lean.Util.CollectLevelParams

namespace Lake
open Lean Meta Elab

def addAndCompileTerm (declName : Name) (value : Expr) : TermElabM Unit := do
  let (value, _) ← Term.levelMVarToParam (← instantiateMVars value)
  let type ← inferType value
  let us := collectLevelParams {} value |>.params
  let value ← instantiateMVars value
  let decl := Declaration.defnDecl {
    name        := declName
    levelParams := us.toList
    type        := type
    value       := value
    hints       := ReducibilityHints.opaque
    safety      := DefinitionSafety.unsafe
  }
  Term.ensureNoUnassignedMVars decl
  addAndCompile decl

unsafe def unsafeEvalTerm (α) [ToExpr α] (term : Syntax) : TermElabM α := do
  let declName := `_eval
  let term ← Term.elabTermEnsuringType term (toTypeExpr α)
  Term.synthesizeSyntheticMVarsNoPostponing
  let env ← getEnv
  try
    addAndCompileTerm declName term
    evalConst α declName
  finally
    setEnv env

@[implementedBy unsafeEvalTerm]
constant evalTerm (α) [ToExpr α] (term : Syntax) : TermElabM α

-- ## ToExpr Instances

instance : ToExpr System.FilePath where
  toExpr p := mkApp (mkConst ``System.FilePath.mk) (toExpr p.toString)
  toTypeExpr := mkConst ``System.FilePath
