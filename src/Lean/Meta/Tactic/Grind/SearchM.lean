/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Types
import Lean.Util.ForEachExpr
public section
namespace Lean.Meta.Grind

/-- Helper type for implementing `finish?` and `grind?` -/
inductive ProofStep where
  | solver (id : Nat)
  | lookahead | mbtc
  | instantiate (thms : List EMatchTheorem) (usedThms : List EMatchTheorem)
  deriving Inhabited

/-- Helper type for implementing `finish?` and `grind?` -/
inductive ProofTrace where
  | done
  | sep (s : ProofStep) (k : ProofTrace)
  | cases (info : SplitInfo) (alts : List ProofTrace)
  deriving Inhabited

/--
A `choice` (aka backtracking) point in the search tree.
-/
structure Choice where
  info?       : Option SplitInfo
  /--
  Goal where the case-split was performed.
  Invariant: `goalPending.mvarId` is not assigned.
  -/
  goalPending : Goal
  /--
  Expression to be assigned to `goalPending.mvarId` if it is not possible to perform
  non-chronological backtracking.
  `proof` is often a `casesOn` application containing meta-variables.
  -/
  proof      : Expr
  /--
  Subgoals that still need to be processed.
  -/
  todo       : List Goal
  traces     : Array ProofTrace := #[]
  generation : Nat
  deriving Inhabited

structure SearchM.State where
  goal        : Goal
  steps       : Array ProofStep := #[]
  trace?      : Option ProofTrace := none
  choiceStack : List Choice := []

abbrev SearchM := StateRefT SearchM.State GrindM

def getGoal : SearchM Goal :=
  return (← get).goal

def setGoal (goal : Goal) : SearchM Unit :=
  modify fun s => { s with goal }

abbrev withCurrGoalContext (x : SearchM α) : SearchM α := do
  (← getGoal).mvarId.withContext x

abbrev liftGoalM (x : GoalM α) : SearchM α := do
  let (a, goal) ← withCurrGoalContext do x.runCore (← get).goal
  modify fun s => { s with goal }
  return a

instance : MonadLift GoalM SearchM where
  monadLift := liftGoalM

@[inline] def SearchM.run (goal : Goal) (x : SearchM α) : GrindM (α × SearchM.State) :=
  goal.mvarId.withContext do StateRefT'.run x { goal }

/--
Given a proof containing meta-variables corresponding to the given subgoals,
create a choice point.
- If there are no choice points, we just close the current goal using `proof`.
- If there is only one subgoal `s`, we close the current goal using `proof`, and
update current goal using `s`.
- If there are more than one `s :: ss`, we create a choice point using the current
goal as the pending goal, and update the current goal with `s`.
-/
def mkChoice (proof : Expr) (subgoals : List Goal) (generation : Nat) (info? : Option SplitInfo := none) : SearchM Unit := do
  assert! !(← isInconsistent)
  match subgoals with
  | [] =>
    (← getGoal).mvarId.assign proof
    modify fun s => { s with goal.inconsistent := true }
  | [subgoal] =>
    (← getGoal).mvarId.assign proof
    setGoal subgoal
  | subgoal :: subgoals =>
    let goalPending ← getGoal
    modify fun s => { s with
      goal := subgoal
      choiceStack := { info?, goalPending, proof, generation, todo := subgoals } :: s.choiceStack
    }

/--
Returns the maximum free variable id occurring in `e`
-/
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
    last.mvarId.assignFalseProof falseProof
    resetChoiceStack

/--
Auxiliary function for implementing `nextGoal`.
It is similar to `nextGoal`, but uses chronological backtracking.
We use it when we cannot extract a proof of `False` from proof used to close the current goal.
Returns `some gen` if a new goal was found for a choice point with generation `gen`,
and returns `none` otherwise.
-/
private def nextChronoGoal? : SearchM (Option Nat) := do
  let mut choices := (← get).choiceStack
  repeat
    match choices with
    | [] => return none
    | choice :: choices' =>
      match choice.todo with
      | [] =>
        -- Choice point has been fully resolved.
        -- Go to next one.
        choice.goalPending.mvarId.assign choice.proof
        choices := choices'
      | goal :: todo =>
        let choice := { choice with todo }
        modify fun s => { s with
          goal
          choiceStack := choice :: choices'
        }
        return some choice.generation
  unreachable!

private def isTargetFalse (mvarId : MVarId) : MetaM Bool := do
  return (← mvarId.getType).isFalse

private def getFalseProof? (mvarId : MVarId) : MetaM (Option Expr) := mvarId.withContext do
  let proof ← instantiateMVars (mkMVar mvarId)
  if (← isTargetFalse mvarId) then
    return some proof
  else if proof.isAppOfArity ``False.elim 2 || proof.isAppOfArity ``False.casesOn 2 then
    return some proof.appArg!
  else
    return none

/--
Select the next goal to be processed from the `choiceStack`.
This function assumes the current goal has been closed (i.e., `inconsistent` is `true`)
Returns `some gen` if a new goal was found for a choice point with generation `gen`,
and returns `none` otherwise.
-/
def nextGoal? : SearchM (Option Nat) := do
  let mut choices := (← get).choiceStack
  if choices.isEmpty then
    return none -- done
  let goal := (← get).goal
  assert! goal.inconsistent
  let some falseProof ← getFalseProof? goal.mvarId
    | nextChronoGoal?
  let mut falseProof := falseProof
  let some max ← goal.mvarId.withContext <| findMaxFVarIdx? falseProof
    | closeLastPending falseProof; return none
  let mut maxFVarIdx := max
  repeat
    let choice :: choices' := choices
      | resetChoiceStack; return none
    let mvarDecl ← choice.goalPending.mvarId.getDecl
    let numIndices := mvarDecl.lctx.numIndices
    if maxFVarIdx < numIndices then
      -- `falseProof` can close `choice.goalPending` since all its free-variables are in scope.
      choice.goalPending.mvarId.assignFalseProof falseProof
      -- keep looking at next choice point
      -- Remark: we may be able to find other choice points using falseProof.
      choices := choices'
    else match choice.todo with
      | [] =>
        -- All subgoals have been solved. We can finally assign `choice.proof` to `goalPending.mvarId`.
        let proof ← instantiateMVars choice.proof
        choice.goalPending.mvarId.assign proof
        if (← isTargetFalse choice.goalPending.mvarId) then
          -- `proof` is a proof of `False`, we can continue using non-chronological backtracking
          falseProof := proof
          let some max ← choice.goalPending.mvarId.withContext <| findMaxFVarIdx? falseProof
            | closeLastPending falseProof; return none
          maxFVarIdx := max
          choices := choices'
        else
          -- `proof` is not a proof of `False`. Thus, we switch to chronological backtracking.
          -- This case can only happen if we are using eager case-splitting with types with
          -- more than one constructor.
          modify fun s => { s with choiceStack := choices' }
          return (← nextChronoGoal?)
      | goal :: todo =>
        -- Found `next` goal to be processed.
        -- Update the current choice point, and current goal.
        let choice := { choice with todo }
        modify fun s => { s with
          goal
          choiceStack := choice :: choices'
        }
        return some choice.generation
  unreachable!

end Lean.Meta.Grind
