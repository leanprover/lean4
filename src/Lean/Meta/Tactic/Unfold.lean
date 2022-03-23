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
      simpTheorems  := {}
      congrTheorems := (← getSimpCongrTheorems)
      config        := Simp.neutralConfig
   }

def unfold (e : Expr) (declName : Name) : MetaM Simp.Result := do
  if let some unfoldThm ← getUnfoldEqnFor? declName  then
    Simp.main e (← getSimpUnfoldContext) (methods := { pre := pre unfoldThm })
  else
    return { expr  := (← deltaExpand e (· == declName)) }
where
  pre (unfoldThm : Name) (e : Expr) : SimpM Simp.Step := do
    match (← withReducible <| Simp.tryTheorem? e { proof := mkConst unfoldThm, name? := some unfoldThm } (fun _ => return none)) with
    | none   => pure ()
    | some r => return Simp.Step.done r
    return Simp.Step.visit { expr := e }

def unfoldTarget (mvarId : MVarId) (declName : Name) : MetaM MVarId := withMVarContext mvarId do
  let target ← instantiateMVars (← getMVarType mvarId)
  let r ← unfold target declName
  applySimpResultToTarget mvarId target r

def unfoldLocalDecl (mvarId : MVarId) (fvarId : FVarId) (declName : Name) : MetaM MVarId := withMVarContext mvarId do
  let localDecl ← getLocalDecl fvarId
  let r ← unfold (← instantiateMVars localDecl.type) declName
  let some (_, mvarId) ← applySimpResultToLocalDecl mvarId fvarId r | unreachable!
  return mvarId

end Lean.Meta
