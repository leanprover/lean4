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

abbrev ConvM := TacticM
abbrev Conv  := Tactic

def convert (lhs : Expr) (conv : ConvM Unit) : TacticM (Expr × Expr) := do
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

@[builtinTactic Lean.Parser.Tactic.Conv.skip] def evalSkip : Tactic := fun stx => do
   liftMetaTactic1 fun mvarId => do
     applyRefl mvarId
     return none

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
