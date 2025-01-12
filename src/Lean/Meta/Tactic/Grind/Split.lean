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
  | ready (numCases : Nat) (isRec := false)
  deriving Inhabited, BEq

private def checkCaseSplitStatus (e : Expr) : GoalM CaseSplitStatus := do
  match_expr e with
  | Or a b =>
    if (← isEqTrue e) then
      if (← isEqTrue a <||> isEqTrue b) then
        return .resolved
      else
        return .ready 2
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
        return .ready 2
    else
      return .notReady
  | Eq _ _ _ =>
    if (← isEqTrue e <||> isEqFalse e) then
      return .ready 2
    else
      return .notReady
  | ite _ c _ _ _ =>
    if (← isEqTrue c <||> isEqFalse c) then
      return .resolved
    else
      return .ready 2
  | dite _ c _ _ _ =>
    if (← isEqTrue c <||> isEqFalse c) then
      return .resolved
    else
      return .ready 2
  | _ =>
    if (← isResolvedCaseSplit e) then
      trace[grind.debug.split] "split resolved: {e}"
      return .resolved
    if let some info := isMatcherAppCore? (← getEnv) e then
      return .ready info.numAlts
    let .const declName .. := e.getAppFn | unreachable!
    if let some info ← isInductivePredicate? declName then
      if (← isEqTrue e) then
        return .ready info.ctors.length info.isRec
    return .notReady

private inductive SplitCandidate where
  | none
  | some (c : Expr) (numCases : Nat) (isRec : Bool)

/-- Returns the next case-split to be performed. It uses a very simple heuristic. -/
private def selectNextSplit? : GoalM SplitCandidate := do
  if (← isInconsistent) then return .none
  if (← checkMaxCaseSplit) then return .none
  go (← get).splitCandidates .none []
where
  go (cs : List Expr) (c? : SplitCandidate) (cs' : List Expr) : GoalM SplitCandidate := do
    match cs with
    | [] =>
      modify fun s => { s with splitCandidates := cs'.reverse }
      if let .some _ numCases isRec := c? then
        let numSplits := (← get).numSplits
        -- We only increase the number of splits if there is more than one case or it is recursive.
        let numSplits := if numCases > 1 || isRec then numSplits + 1 else numSplits
        -- Remark: we reset `numEmatch` after each case split.
        -- We should consider other strategies in the future.
        modify fun s => { s with numSplits, numEmatch := 0 }
      return c?
    | c::cs =>
    match (← checkCaseSplitStatus c) with
    | .notReady => go cs c? (c::cs')
    | .resolved => go cs c? cs'
    | .ready numCases isRec =>
    match c? with
    | .none => go cs (.some c numCases isRec) cs'
    | .some c' numCases' _ =>
     let isBetter : GoalM Bool := do
       if numCases == 1 && !isRec && numCases' > 1 then
         return true
       if (← getGeneration c) < (← getGeneration c') then
         return true
       return numCases < numCases'
     if (← isBetter) then
        go cs (.some c numCases isRec) (c'::cs')
      else
        go cs c? (c::cs')

/-- Constructs a major premise for the `cases` tactic used by `grind`. -/
private def mkCasesMajor (c : Expr) : GoalM Expr := do
  match_expr c with
  | And a b => return mkApp3 (mkConst ``Grind.or_of_and_eq_false) a b (← mkEqFalseProof c)
  | ite _ c _ _ _ => return mkEM c
  | dite _ c _ _ _ => return mkEM c
  | Eq _ a b =>
    if (← isEqTrue c) then
      return mkApp3 (mkConst ``Grind.of_eq_eq_true) a b (← mkEqTrueProof c)
    else
      return mkApp3 (mkConst ``Grind.of_eq_eq_false) a b (← mkEqFalseProof c)
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
    let .some c numCases isRec ← selectNextSplit?
      | return none
    let gen ← getGeneration c
    let genNew := if numCases > 1 || isRec then gen+1 else gen
    trace_goal[grind.split] "{c}, generation: {gen}"
    let mvarIds ← if (← isMatcherApp c) then
      casesMatch (← get).mvarId c
    else
      let major ← mkCasesMajor c
      cases (← get).mvarId major
    let goal ← get
    let goals := mvarIds.map fun mvarId => { goal with mvarId }
    let goals ← introNewHyp goals [] genNew
    return some goals
  return goals?

end Lean.Meta.Grind
