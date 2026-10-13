/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Lean.Elab.Tactic.Rewrite
import Lean.Linter.Init
import Lean.Meta.Tactic.TryThis

public section

namespace Lean.Elab.Tactic
open scoped Lean.Parser.Tactic

/--
Enables the unnecessary `rwa` linter, which reports when `rw` closes the goal without needing the
final closing step.
-/
register_builtin_option linter.unnecessaryRwa : Bool := {
  defValue := true
  descr := "enable the unnecessary `rwa` linter"
}

private def logUnnecessaryRwa (initialState : SavedState) (ref : Syntax)
    (replacement : TSyntax `tactic) : TacticM Unit := do
  unless Linter.getLinterValue linter.unnecessaryRwa (← Linter.getLinterOptions) do
    return
  let mut msg := m!"`rw` already closes the goal"
  if ← Meta.Tactic.TryThis.isValidTactic initialState replacement then
    let suggestion : Meta.Hint.Suggestion := {
      suggestion := replacement
      span? := ref
      diffGranularity := .none
    }
    let hint ← MessageData.hint "Use `rw` instead of `rwa`:" #[suggestion] (ref? := ref)
    msg := msg ++ hint
  Linter.logLint linter.unnecessaryRwa ref msg

private def evalRwaCore (ref : Syntax) (rewrite : TacticM α) (replacement : TSyntax `tactic)
    (close : α → TacticM Unit) : TacticM Unit :=
  Tactic.focus do
    let initialState ← saveState
    let rewriteResult ← rewrite
    let closedByRfl ← Tactic.focus <|
      (do
        evalTactic (← `(tactic| with_reducible rfl))
        pure true) <|>
      (do
        close rewriteResult
        pure false)
    let sideGoals ← getUnsolvedGoals
    if closedByRfl && sideGoals.isEmpty then
      logUnnecessaryRwa initialState ref replacement
    evalTactic (← `(tactic| all_goals (first | with_reducible rfl | assumption | skip)))

private def closeUsingFVar (fvarId : FVarId) : TacticM Unit := withMainContext do
  let mvarId ← getMainGoal
  let fvar := mkFVar fvarId
  let fvarType ← Meta.inferType fvar
  let target ← mvarId.getType
  unless ← Meta.withAssignableSyntheticOpaque <|
      Meta.isDefEq fvarType target do
    throwError "Type mismatch: The rewritten hypothesis{indentExpr fvar}\n\
      {← Meta.mkHasTypeButIsExpectedMsg fvarType target}"
  closeMainGoal `rwa fvar

@[builtin_tactic Lean.Parser.Tactic.rwa]
def evalRwa : Tactic := fun stx => do
  match stx with
  | `(tactic| rwa $rws:rwRuleSeq) =>
    evalRwaCore stx
      (evalTactic (← `(tactic| rewrite $rws:rwRuleSeq)))
      (← `(tactic| rw $rws:rwRuleSeq))
      fun _ => do evalTactic (← `(tactic| assumption))
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.rwaAt]
def evalRwaAt : Tactic := fun stx => do
  match stx with
  | `(tactic| rwa $rws:rwRuleSeq at $h:term) => do
    evalRwaCore stx
      (do
        let fvarId ← getFVarId h
        foldRWRulesSeq stx[0] rws fvarId fun fvarId symm term =>
          rewriteLocalDeclCore term symm fvarId)
      (← `(tactic| rw $rws:rwRuleSeq at $h:term))
      closeUsingFVar
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
