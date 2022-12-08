/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.Simp.Main

namespace Lean.Meta

private def getSimpUnfoldContext : MetaM Simp.Context :=
   return {
      congrTheorems := (← getSimpCongrTheorems)
      config        := Simp.neutralConfig
   }

def unfold (e : Expr) (declName : Name) : MetaM Simp.Result := do
  if let some unfoldThm ← getUnfoldEqnFor? declName  then
    (·.1) <$> Simp.main e (← getSimpUnfoldContext) (methods := { pre := pre unfoldThm })
  else
    return { expr  := (← deltaExpand e (· == declName)) }
where
  pre (unfoldThm : Name) (e : Expr) : SimpM Simp.Step := do
    match (← withReducible <| Simp.tryTheorem? e { origin := .decl unfoldThm, proof := mkConst unfoldThm, rfl := (← isRflTheorem unfoldThm) } (fun _ => return none)) with
    | none   => pure ()
    | some r => match (← reduceMatcher? r.expr) with
      | .reduced e' => return Simp.Step.done { r with expr := e' }
      | _ => return Simp.Step.done r
    return Simp.Step.visit { expr := e }

def unfoldTarget (mvarId : MVarId) (declName : Name) : MetaM MVarId := mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let r ← unfold target declName
  if r.expr == target then throwError "tactic 'unfold' failed to unfold '{declName}' at{indentExpr target}"
  applySimpResultToTarget mvarId target r

def unfoldLocalDecl (mvarId : MVarId) (fvarId : FVarId) (declName : Name) : MetaM MVarId := mvarId.withContext do
  let type ← fvarId.getType
  let r ← unfold (← instantiateMVars type) declName
  if r.expr == type then throwError "tactic 'unfold' failed to unfold '{declName}' at{indentExpr type}"
  let some (_, mvarId) ← applySimpResultToLocalDecl mvarId fvarId r (mayCloseGoal := false) | unreachable!
  return mvarId

end Lean.Meta
