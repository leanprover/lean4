/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.CasesMatch

namespace Lean.Meta.Grind

inductive CaseSplitStatus where
  | resolved
  | notReady
  | ready
  deriving Inhabited, BEq

private def checkCaseSplitStatus (e : Expr) : GoalM CaseSplitStatus := do
  match_expr e with
  | Or a b =>
    if (← isEqTrue e) then
      if (← isEqTrue a <||> isEqTrue b) then
        return .resolved
      else
        return .ready
    else if (← isEqFalse e) then
      return .resolved
    else
      return .notReady
  | And a b =>
    if (← isEqTrue e) then
      return .resolved
    else if (← isEqFalse e) then
      if (← isEqFalse a <||> isEqFalse b) then
        return .resolved
      else
        return .ready
    else
      return .notReady
  | ite _ c _ _ _ =>
    if (← isEqTrue c <||> isEqFalse c) then
      return .resolved
    else
      return .ready
  | dite _ c _ _ _ =>
    if (← isEqTrue c <||> isEqFalse c) then
      return .resolved
    else
      return .ready
  | _ =>
    if (← isResolvedCaseSplit e) then
      trace[grind.debug.split] "split resolved: {e}"
      return .resolved
    if (← isMatcherApp e) then
      return .ready
    let .const declName .. := e.getAppFn | unreachable!
    if (← isInductivePredicate declName <&&> isEqTrue e) then
      return .ready
    return .notReady

/-- Returns the next case-split to be performed. It uses a very simple heuristic. -/
private def selectNextSplit? : GoalM (Option Expr) := do
  if (← isInconsistent) then return none
  if (← checkMaxCaseSplit) then return none
  go (← get).splitCandidates none []
where
  go (cs : List Expr) (c? : Option Expr) (cs' : List Expr) : GoalM (Option Expr) := do
    match cs with
    | [] =>
      modify fun s => { s with splitCandidates := cs'.reverse }
      if c?.isSome then
        -- Remark: we reset `numEmatch` after each case split.
        -- We should consider other strategies in the future.
        modify fun s => { s with numSplits := s.numSplits + 1, numEmatch := 0 }
      return c?
    | c::cs =>
    match (← checkCaseSplitStatus c) with
    | .notReady => go cs c? (c::cs')
    | .resolved => go cs c? cs'
    | .ready =>
    match c? with
    | none => go cs (some c) cs'
    | some c' =>
      if (← getGeneration c) < (← getGeneration c') then
        go cs (some c) (c'::cs')
      else
        go cs c? (c::cs')

/-- Constructs a major premise for the `cases` tactic used by `grind`. -/
private def mkCasesMajor (c : Expr) : GoalM Expr := do
  match_expr c with
  | And a b => return mkApp3 (mkConst ``Grind.or_of_and_eq_false) a b (← mkEqFalseProof c)
  | ite _ c _ _ _ => return mkEM c
  | dite _ c _ _ _ => return mkEM c
  | _ => return mkApp2 (mkConst ``of_eq_true) c (← mkEqTrueProof c)

/-- Introduces new hypotheses in each goal. -/
private def introNewHyp (goals : List Goal) (acc : List Goal) (generation : Nat) : GrindM (List Goal) := do
  match goals with
  | [] => return acc.reverse
  | goal::goals => introNewHyp goals ((← intros generation goal) ++ acc) generation

/--
Selects a case-split from the list of candidates,
and returns a new list of goals if successful.
-/
def splitNext : GrindTactic := fun goal => do
  let (goals?, _) ← GoalM.run goal do
    let some c ← selectNextSplit?
      | return none
    let gen ← getGeneration c
    trace_goal[grind.split] "{c}, generation: {gen}"
    let mvarIds ← if (← isMatcherApp c) then
      casesMatch (← get).mvarId c
    else
      let major ← mkCasesMajor c
      cases (← get).mvarId major
    let goal ← get
    let goals := mvarIds.map fun mvarId => { goal with mvarId }
    let goals ← introNewHyp goals [] (gen+1)
    return some goals
  return goals?

end Lean.Meta.Grind
