/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Replace
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.BuiltinTactic

namespace Lean.Elab.Tactic.Conv
open Meta

def convert (lhs : Expr) (conv : TacticM Unit) : TacticM (Expr × Expr) := do
  let lhsType ← inferType lhs
  let rhs ← mkFreshExprMVar lhsType
  let targetNew ← mkEq lhs rhs
  let newGoal ← mkFreshExprSyntheticOpaqueMVar targetNew
  let savedGoals ← getGoals
  try
    setGoals [newGoal.mvarId!]
    withReader (fun ctx => { ctx with inConv := true }) conv
    pruneSolvedGoals
    for mvarId in (← getGoals) do
      try
        applyRefl mvarId
      catch _ =>
        throwError "convert tactic failed, there are unsolved goal"
    pure ()
  finally
    setGoals savedGoals
  return (← instantiateMVars rhs, ← instantiateMVars newGoal)

def getLhsRhs : TacticM (Expr × Expr) :=
  withMainContext do
    let some (_, lhs, rhs) ← matchEq? (← getMainTarget) | throwError "invalid 'conv' goal"
    return (lhs, rhs)

def getLhs : TacticM Expr :=
  return (← getLhsRhs).1

def getRhs : TacticM Expr :=
  return (← getLhsRhs).2

/-- `⊢ lhs = rhs` ~~> `⊢ lhs' = rhs` using `h : lhs = lhs'`. -/
def updateLhs (lhs' : Expr) (h : Expr) : TacticM Unit := do
  let rhs ← getRhs
  let newGoal ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhs' rhs)
  assignExprMVar (← getMainGoal) (← mkEqTrans h newGoal)
  replaceMainGoal [newGoal.mvarId!]

/-- Replace `lhs` with the definitionally equal `lhs'`. -/
def changeLhs (lhs' : Expr) : TacticM Unit := do
  let rhs ← getRhs
  liftMetaTactic1 fun mvarId => do
    replaceTargetDefEq mvarId (← mkEq lhs' rhs)

@[builtinTactic Lean.Parser.Tactic.Conv.skip] def evalSkip : Tactic := fun stx => do
   liftMetaTactic1 fun mvarId => do
     applyRefl mvarId
     return none

@[builtinTactic Lean.Parser.Tactic.Conv.whnf] def evalWhnf : Tactic := fun stx =>
   withMainContext do
     let lhs ← getLhs
     changeLhs (← whnf lhs)

@[builtinTactic Lean.Parser.Tactic.Conv.convSeq1Indented] def evalConvSeq1Indented : Tactic := fun stx => do
  evalTacticSeq1Indented stx

@[builtinTactic Lean.Parser.Tactic.Conv.convSeqBracketed] def evalConvSeqBracketed : Tactic := fun stx => do
  evalTacticSeqBracketed stx

@[builtinTactic Lean.Parser.Tactic.Conv.convSeq] def evalConvSeq : Tactic := fun stx => do
  evalTactic stx[0]

private def convTarget (conv : Syntax) : TacticM Unit := do
   let target ← getMainTarget
   let (targetNew, proof) ← convert target (evalTactic conv)
   liftMetaTactic1 fun mvarId => replaceTargetEq mvarId targetNew proof

@[builtinTactic Lean.Parser.Tactic.Conv.conv] def evalConv : Tactic := fun stx => do
  match stx with
  | `(tactic| conv $[at $loc]? $[in $e]? => $code) =>
    -- TODO: implement `at` and `in` support
    convTarget code
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.Conv
