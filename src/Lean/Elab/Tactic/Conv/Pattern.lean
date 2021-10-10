/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Tactic.Simp
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

private def getContext : MetaM Simp.Context := do
  return {
    simpLemmas    := {}
    congrLemmas   := (← getCongrLemmas)
    config.zeta   := false
    config.beta   := false
    config.eta    := false
    config.iota   := false
    config.proj   := false
    config.decide := false
  }

def matchPattern (pattern : AbstractMVarsResult) (e : Expr) : MetaM Bool :=
  withNewMCtxDepth do
    /- TODO: check whether the following is a performance bottleneck. If it is, recall that we used `AbstractMVarsResult` to make
       sure we can match the pattern inside of binders. So, it is not needed in most cases. -/
    let (_, _, pattern) ← openAbstractMVarsResult pattern
    withReducible <| isDefEqGuarded pattern e

private def pre (pattern : AbstractMVarsResult) (found? : IO.Ref (Option Expr)) (e : Expr) : SimpM Simp.Step := do
  if (← found?.get).isSome then
    return Simp.Step.visit { expr := e }
  else if (← matchPattern pattern e) then
    let (rhs, newGoal) ← mkConvGoalFor e
    found?.set newGoal
    return Simp.Step.done { expr := rhs, proof? := newGoal }
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
    let pattern ← Term.withoutPending <| Term.elabTerm p none
    let patternA ← abstractMVars pattern
    let lhs ← getLhs
    match (← findPattern? patternA lhs) with
    | none => throwError "'pattern' conv tactic failed, pattern was not found{indentExpr pattern}"
    | some (mvarId', result) =>
      updateLhs result.expr (← result.getProof)
      applyRefl (← getMainGoal)
      replaceMainGoal [mvarId']
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
