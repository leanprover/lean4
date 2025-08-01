/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Eqns
public import Lean.Meta.Tactic.Delta
public import Lean.Meta.Tactic.Simp.Main

public section

namespace Lean.Meta

private def getSimpUnfoldContext : MetaM Simp.Context := do
   Simp.mkContext
      (congrTheorems := (← getSimpCongrTheorems))
      (config        := { Simp.neutralConfig with letToHave := true })

def unfold (e : Expr) (declName : Name) : MetaM Simp.Result := do
  if let some unfoldThm ← getUnfoldEqnFor? declName  then
    (·.1) <$> Simp.main e (← getSimpUnfoldContext) (methods := { pre := pre unfoldThm })
  else
    return { expr  := (← deltaExpand e (· == declName)) }
where
  pre (unfoldThm : Name) (e : Expr) : SimpM Simp.Step := do
    match (← withReducible <| Simp.tryTheorem? e { origin := .decl unfoldThm, proof := mkConst unfoldThm, rfl := (← isRflTheorem unfoldThm) }) with
    | none   => pure ()
    | some r => match (← reduceMatcher? r.expr) with
      | .reduced e' => return .done { r with expr := e' }
      | _ => return .done r
    return .continue

def unfoldTarget (mvarId : MVarId) (declName : Name) : MetaM MVarId := mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let r ← unfold target declName
  if r.expr == target then throwError "Tactic `unfold` failed to unfold `{declName}` in{indentExpr target}"
  applySimpResultToTarget mvarId target r

def unfoldLocalDecl (mvarId : MVarId) (fvarId : FVarId) (declName : Name) : MetaM MVarId := mvarId.withContext do
  let type ← fvarId.getType
  let r ← unfold (← instantiateMVars type) declName
  if r.expr == type then throwError "Tactic `unfold` failed to unfold `{declName}` in{indentExpr type}"
  let some (_, mvarId) ← applySimpResultToLocalDecl mvarId fvarId r (mayCloseGoal := false) | unreachable!
  return mvarId

def zetaDeltaTarget (mvarId : MVarId) (declFVarId : FVarId) : MetaM MVarId := mvarId.withContext do
  let target ← instantiateMVars (← mvarId.getType)
  let target' ← Meta.zetaDeltaFVars target #[declFVarId]
  if target' == target then throwError "Tactic `unfold` failed to unfold `{Expr.fvar declFVarId}` in{indentExpr target}"
  mvarId.replaceTargetDefEq target'

def zetaDeltaLocalDecl (mvarId : MVarId) (fvarId : FVarId) (declFVarId : FVarId) : MetaM MVarId := mvarId.withContext do
  let type ← fvarId.getType
  let type' ← Meta.zetaDeltaFVars (← instantiateMVars type) #[declFVarId]
  if type' == type then throwError "Tactic `unfold` failed to unfold `{Expr.fvar fvarId}` in{indentExpr type}"
  mvarId.replaceLocalDeclDefEq fvarId type'

end Lean.Meta
