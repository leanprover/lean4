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

/-- Given `c`, the condition of an `if-then-else`, check whether we need to case-split on the `if-then-else` or not -/
private def checkIteCondStatus (c : Expr) : GoalM CaseSplitStatus := do
  if (← isEqTrue c <||> isEqFalse c) then
    return .resolved
  else
    return .ready 2

/--
Given `e` of the form `a ∨ b`, check whether we are ready to case-split on `e`.
That is, `e` is `True`, but neither `a` nor `b` is `True`."
-/
private def checkDisjunctStatus (e a b : Expr) : GoalM CaseSplitStatus := do
  if (← isEqTrue e) then
    if (← isEqTrue a <||> isEqTrue b) then
      return .resolved
    else
      return .ready 2
  else if (← isEqFalse e) then
    return .resolved
  else
    return .notReady

/--
Given `e` of the form `a ∧ b`, check whether we are ready to case-split on `e`.
That is, `e` is `False`, but neither `a` nor `b` is `False`.
 -/
private def checkConjunctStatus (e a b : Expr) : GoalM CaseSplitStatus := do
  if (← isEqTrue e) then
    return .resolved
  else if (← isEqFalse e) then
    if (← isEqFalse a <||> isEqFalse b) then
      return .resolved
    else
      return .ready 2
  else
    return .notReady

/--
Given `e` of the form `@Eq Prop a b`, check whether we are ready to case-split on `e`.
There are two cases:
1- `e` is `True`, but neither both `a` and `b` are `True`, nor both `a` and `b` are `False`.
2- `e` is `False`, but neither `a` is `True` and `b` is `False`, nor `a` is `False` and `b` is `True`.
-/
private def checkIffStatus (e a b : Expr) : GoalM CaseSplitStatus := do
  if (← isEqTrue e) then
    if (← (isEqTrue a <&&> isEqTrue b) <||> (isEqFalse a <&&> isEqFalse b)) then
      return .resolved
    else
      return .ready 2
  else if (← isEqFalse e) then
    if (← (isEqTrue a <&&> isEqFalse b) <||> (isEqFalse a <&&> isEqTrue b)) then
      return .resolved
    else
      return .ready 2
  else
    return .notReady

/-- Returns `true` is `c` is congruent to a case-split that was already performed. -/
private def isCongrToPrevSplit (c : Expr) : GoalM Bool := do
  (← get).resolvedSplits.foldM (init := false) fun flag { expr := c' } => do
    if flag then
      return true
    else
      return isCongruent (← get).enodes c c'

private def checkCaseSplitStatus (e : Expr) : GoalM CaseSplitStatus := do
  match_expr e with
  | Or a b => checkDisjunctStatus e a b
  | And a b => checkConjunctStatus e a b
  | Eq _ a b => checkIffStatus e a b
  | ite _ c _ _ _ => checkIteCondStatus c
  | dite _ c _ _ _ => checkIteCondStatus c
  | _ =>
    if (← isResolvedCaseSplit e) then
      trace_goal[grind.debug.split] "split resolved: {e}"
      return .resolved
    if (← isCongrToPrevSplit e) then
      return .resolved
    if let some info := isMatcherAppCore? (← getEnv) e then
      return .ready info.numAlts
    if let .const declName .. := e.getAppFn then
      if let some info ← isInductivePredicate? declName then
        if (← isEqTrue e) then
          return .ready info.ctors.length info.isRec
    if e.isFVar then
      let type ← whnfD (← inferType e)
      let report : GoalM Unit := do
        reportIssue! "cannot perform case-split on {e}, unexpected type{indentExpr type}"
      let .const declName _ := type.getAppFn | report; return .resolved
      let .inductInfo info ← getConstInfo declName | report; return .resolved
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
  | _ =>
    if (← isEqTrue c) then
      return mkOfEqTrueCore c (← mkEqTrueProof c)
    else
      return c

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
    markCaseSplitAsResolved c
    trace_goal[grind.split] "{c}, generation: {gen}"
    let mvarIds ← if (← isMatcherApp c) then
      casesMatch (← get).mvarId c
    else
      let major ← mkCasesMajor c
      if (← getConfig).trace then
        if let .const declName _ := (← whnfD (← inferType major)).getAppFn then
          saveCases declName false
      cases (← get).mvarId major
    let goal ← get
    let numSubgoals := mvarIds.length
    let goals := mvarIds.mapIdx fun i mvarId => { goal with mvarId, casesTrace := { expr := c, i, num := numSubgoals } :: goal.casesTrace }
    let goals ← introNewHyp goals [] genNew
    return some goals
  return goals?

end Lean.Meta.Grind
