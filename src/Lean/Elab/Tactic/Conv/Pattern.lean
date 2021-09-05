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

private def pre (pattern : Expr) (found? : IO.Ref (Option Expr)) (e : Expr) : SimpM Simp.Step := do
  if (← withReducible <| isDefEqGuarded pattern e) then
    let (rhs, newGoal) ← mkConvGoalFor e
    found?.set newGoal
    return Simp.Step.done { expr := rhs, proof? := newGoal }
  else
    return Simp.Step.visit { expr := e }

private def findPattern? (pattern : Expr) (e : Expr) : MetaM (Option (MVarId × Simp.Result)) := do
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
    let lhs ← getLhs
    match (← findPattern? pattern lhs) with
    | none => throwError "'pattern' conv tactic failed, pattern was not found{indentExpr pattern}"
    | some (mvarId', result) =>
      updateLhs result.expr (← result.getProof)
      applyRefl (← getMainGoal)
      replaceMainGoal [mvarId']
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
