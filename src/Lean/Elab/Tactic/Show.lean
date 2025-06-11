/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Lean.Elab.Tactic.Change

namespace Lean.Elab.Tactic
open Meta
/-!
# Implementation of the `show` tactic

The `show p` tactic finds the first goal that `p` unifies with and brings it to the front of the
goal list. If there were a `first_goal` combinator, it would be like `first_goal change p`.
-/

@[inline]
private def withCaptureLog (x : TacticM Unit) : TacticM MessageLog := do
  let prevMessages := (← getThe Core.State).messages
  modifyThe Core.State (fun s => { s with messages := {} })

  withTheReader Core.Context (fun ctx => { ctx with suppressElabErrors := false }) x

  let newMessages := (← getThe Core.State).messages
  modifyThe Core.State (fun s => { s with messages := prevMessages ++ newMessages })
  return newMessages

def elabShow (newType : Term) : TacticM Unit := do
  let (goal :: goals) ← getGoals | throwNoGoalsToBeSolved
  let state ← saveState

  Tactic.tryCatch (do
      let log ← withCaptureLog (tryGoal newType goal goals [])
      if log.hasErrors then
        let errState ← saveState
        state.restore true
        go errState none newType goals [])
    (fun ex => do
      let errState ← saveState
      state.restore true
      go errState (some ex) newType goals [])
where
  go (errState : SavedState) (err : Option Exception) (newType : Term) (goals : List MVarId) (prevRev : List MVarId) : TacticM Unit := do
    match goals with
    | [] =>
      errState.restore true
      if let some ex := err then
        throw ex
    | goal :: goals =>
      /-
      Save state manually to make sure that the info state is reverted,
      since `elabChange` elaborates the pattern each time.
      -/
      let state ← saveState
      Tactic.tryCatch
        (withoutRecover (tryGoal newType goal goals prevRev))
        fun _ => do
          state.restore true
          go errState err newType goals (goal :: prevRev)
  tryGoal (newType : Term) (goal : MVarId) (goals : List MVarId) (prevRev : List MVarId) : TacticM Unit := do
    let type ← goal.getType
    let tag ← goal.getTag
    goal.withContext do
      let (tgt', mvars) ← withCollectingNewGoalsFrom
        (elabChange type newType (defeqError (prevRev.isEmpty && !goals.isEmpty)))
        tag `show
      let goal' ← goal.replaceTargetDefEq tgt'
      let newGoals := goal' :: prevRev.reverseAux (mvars ++ goals)
      setGoals newGoals
  defeqError (firstOfMany : Bool) (p tgt : Expr) : MetaM MessageData := do
    let mut msg := m!"\
      'show' tactic failed, pattern{indentExpr p}\n\
      is not definitionally equal to target{indentExpr tgt}"
    if firstOfMany then
      msg := msg ++ "\nor to the target of any other goal"
    return msg

@[builtin_tactic «show»] elab_rules : tactic
  | `(tactic| show $newType:term) => elabShow newType

end Lean.Elab.Tactic
