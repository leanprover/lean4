/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic
import Lean.HeadIndex

namespace Lean.Elab.Tactic.Conv
open Meta

private def getContext : MetaM Simp.Context := do
  return {
    simpTheorems  := {}
    congrTheorems := (← getSimpCongrTheorems)
    config        := Simp.neutralConfig
  }

partial def matchPattern? (pattern : AbstractMVarsResult) (e : Expr) : MetaM (Option (Expr × Array Expr)) :=
  withNewMCtxDepth do
    /- TODO: check whether the following is a performance bottleneck. If it is, recall that we used `AbstractMVarsResult` to make
       sure we can match the pattern inside of binders. So, it is not needed in most cases. -/
    let (_, _, pattern) ← openAbstractMVarsResult pattern
    let rec go? (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
      if e.toHeadIndex != pattern.toHeadIndex then
        return none
      else if (← isDefEqGuarded pattern e) then
        return some (e, #[])
      else if e.isApp then
        return (← go? e.appFn!).map fun (f, extra) => (f, extra.push e.appArg!)
      else
        return none
    withReducible <| go? e

private def pre (pattern : AbstractMVarsResult) (found? : IO.Ref (Option Expr)) (e : Expr) : SimpM Simp.Step := do
  if (← found?.get).isSome then
    return Simp.Step.visit { expr := e }
  else if let some (e, extraArgs) ← matchPattern? pattern e then
    let (rhs, newGoal) ← mkConvGoalFor e
    found?.set newGoal
    let mut proof := newGoal
    for extraArg in extraArgs do
      proof ← mkCongrFun proof extraArg
    return Simp.Step.done { expr := mkAppN rhs extraArgs, proof? := proof }
  else
    return Simp.Step.visit { expr := e }

private def findPattern? (pattern : AbstractMVarsResult) (e : Expr) : MetaM (Option (MVarId × Simp.Result)) := do
  let found? ← IO.mkRef none
  let result ← Simp.main e (← getContext) (methods := { pre := pre pattern found? })
  if let some newGoal ← found?.get then
    return some (newGoal.mvarId!, result)
  else
    return none

@[builtinTactic Lean.Parser.Tactic.Conv.pattern] def evalPattern : Tactic := fun stx => withMainContext do
  match stx with
  | `(conv| pattern $p) =>
    let patternA ←
       withTheReader Term.Context (fun ctx => { ctx with ignoreTCFailures := true }) <|
       Term.withoutModifyingElabMetaStateWithInfo <| withRef p <|
       Term.withoutErrToSorry do
         abstractMVars (← Term.elabTerm p none)
    let lhs ← getLhs
    match (← findPattern? patternA lhs) with
    | none => throwError "'pattern' conv tactic failed, pattern was not found{indentExpr patternA.expr}"
    | some (mvarId', result) =>
      updateLhs result.expr (← result.getProof)
      applyRefl (← getMainGoal)
      replaceMainGoal [mvarId']
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
