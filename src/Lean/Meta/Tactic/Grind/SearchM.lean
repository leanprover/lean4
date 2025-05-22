/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ForEachExpr
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind
/--
A `choice` (aka backtracking) point in the search tree.
-/
structure Choice where
  /--
  Goal where the case-split was performed.
  Invariant: `goalOld.mvarId` is not assigned.
  Invariant: `goalOld.mvarId.getType` is `False`.
  -/
  goalPending : Goal
  /--
  Expression to be assigned to `goalOld.mvarId` if it is not possible to perform
  non-chronological backtracking.
  `val` is often a `casesOn` application.
  -/
  val      : Expr
  /--
  Subgoals that still need to be processed.
  -/
  todo     : List Goal
  deriving Inhabited

structure SearchM.State where
  goal : Goal
  choiceStack : List Choice := []

abbrev SearchM := StateRefT SearchM.State GrindM

abbrev liftGoalM (x : GoalM α) : SearchM α := do
  let (a, goal) ← x.runCore (← get).goal
  modify fun s => { s with goal }
  return a

instance : MonadLift GoalM SearchM where
  monadLift := liftGoalM

@[inline] def SearchM.run (goal : Goal) (x : SearchM α) : GrindM (α × SearchM.State) :=
  goal.mvarId.withContext do StateRefT'.run x { goal }

private def findMaxFVarIdx? (e : Expr) : MetaM (Option Nat) := do
  let go (e : Expr) : StateT (Option Nat) MetaM Bool := do
    unless e.hasFVar do return false
    let .fvar fvarId := e | return true
    let localDecl ← fvarId.getDecl
    modify fun
      | none => some localDecl.index
      | some index => some (max index localDecl.index)
    return false
  let (_, s?) ← e.forEach' go |>.run none
  return s?

private def resetChoiceStack : SearchM Unit :=
  modify fun s => { s with choiceStack := [] }

/--
Use `falseProof` to close the last pending goal in the choice stack,
and reset it.
We use this function when `falseProof` does not have free variables.
-/
private def closeLastPending (falseProof : Expr) : SearchM Unit := do
  let choices := (← get).choiceStack
  if h : choices.isEmpty then
    return
  else
    let last := choices.getLast (ne_of_apply_ne List.isEmpty h) |>.goalPending
    last.mvarId.assign falseProof
    resetChoiceStack

/--
Select the next goal to be processed from the `choiceStack`.
This function assumes the current goal has been closed (i.e., `inconsistent` is `true`)
Returns `true` if a new goal was found, and returns `false` otherwise.
When the result is `false`, the initial goal has been solved.
-/
def nextGoal : SearchM Bool := do
  let mut choices := (← get).choiceStack
  if choices.isEmpty then
    return false -- done
  let goal := (← get).goal
  assert! goal.inconsistent
  let mut falseProof ← instantiateMVars (mkMVar goal.mvarId)
  let some max ← findMaxFVarIdx? falseProof
    | closeLastPending falseProof; return false
  -- proof does not have free variables, thus it can close any goal in the choiceStack
  let mut maxFVarIdx := max
  repeat
    let choice :: choices' := choices
      | resetChoiceStack; return false
    let mvarDecl ← choice.goalPending.mvarId.getDecl
    let numIndices := mvarDecl.lctx.numIndices
    if maxFVarIdx < numIndices then
      -- `falseProof` can close `choice.goalOld` since all its free-variables are in scope.
      choice.goalPending.mvarId.assign falseProof
      -- keep looking at next choice point
      choices := choices'
    else match choice.todo with
      | [] =>
        -- All subgoals have been solved. We can finally assign `choice.val` to `goalOld.mvarId`.
        -- Actually, `choice.val` is a new proof for `False`
        falseProof := choice.val
        choice.goalPending.mvarId.assign falseProof
        let some max ← findMaxFVarIdx? falseProof
          | closeLastPending falseProof; return false
        maxFVarIdx := max
        choices := choices'
      | goal :: todo =>
        -- Found `next` goal to be processed.
        -- Update the current choice point, and current goal.
        let choice := { choice with todo }
        modify fun s => { s with
          goal
          choiceStack := choice :: choices'
        }
        return true
  unreachable!

end Lean.Meta.Grind
