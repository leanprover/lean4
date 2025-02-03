/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.CasesMatch
import Lean.Meta.Tactic.Grind.Injection
import Lean.Meta.Tactic.Grind.Core
import Lean.Meta.Tactic.Grind.Combinators

namespace Lean.Meta.Grind

private inductive IntroResult where
  | done
  | newHyp (fvarId : FVarId) (goal : Goal)
  | newDepHyp (goal : Goal)
  | newLocal (fvarId : FVarId) (goal : Goal)
  deriving Inhabited

/--
Similar to `Grind.preprocess`, but does not simplify `e` if
`isMatchCondCandidate` (aka `Simp.isEqnThmHypothesis`) is `true`.
We added this feature because it may be coming from external sources
(e.g., manually applying an function induction principle before invoking `grind`).
-/
private def preprocessHypothesis (e : Expr) : GoalM Simp.Result := do
  if isMatchCondCandidate e then
    preprocess (markAsMatchCond e)
  else
    preprocess e

private def introNext (goal : Goal) (generation : Nat) : GrindM IntroResult := do
  let target ← goal.mvarId.getType
  if target.isArrow then
    let (r, _) ← GoalM.run goal do
      let mvarId := (← get).mvarId
      let p := target.bindingDomain!
      if !(← isProp p) then
        let (fvarId, mvarId) ← mvarId.intro1P
        return .newLocal fvarId { (← get) with mvarId }
      else
        let tag ← mvarId.getTag
        let q := target.bindingBody!
        let r ← preprocessHypothesis p
        let fvarId ← mkFreshFVarId
        let lctx := (← getLCtx).mkLocalDecl fvarId target.bindingName! r.expr target.bindingInfo!
        let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances) q .syntheticOpaque tag
        let mvarIdNew := mvarNew.mvarId!
        mvarIdNew.withContext do
          let h ← mkLambdaFVars #[mkFVar fvarId] mvarNew
          match r.proof? with
          | some he =>
            let hNew := mkAppN (mkConst ``Lean.Grind.intro_with_eq) #[p, r.expr, q, he, h]
            mvarId.assign hNew
            return .newHyp fvarId { (← get) with mvarId := mvarIdNew }
          | none =>
            -- `p` and `p'` are definitionally equal
            mvarId.assign h
            return .newHyp fvarId { (← get) with mvarId := mvarIdNew }
    return r
  else if target.isLet || target.isForall || target.isLetFun then
    let (fvarId, mvarId) ← goal.mvarId.intro1P
    mvarId.withContext do
      let localDecl ← fvarId.getDecl
      if (← isProp localDecl.type) then
        -- Add a non-dependent copy
        let mvarId ← mvarId.assert (← mkFreshUserName localDecl.userName) localDecl.type (mkFVar fvarId)
        return .newDepHyp { goal with mvarId }
      else
        let goal := { goal with mvarId }
        if target.isLet || target.isLetFun then
          let goal ← GoalM.run' goal do
            let v := (← fvarId.getDecl).value
            let r ← preprocessHypothesis v
            let x ← shareCommon (mkFVar fvarId)
            addNewEq x r.expr (← r.getProof) generation
          return .newLocal fvarId goal
        else
          return .newLocal fvarId goal
  else
    return .done

private def isEagerCasesCandidate (goal : Goal) (type : Expr) : Bool := Id.run do
  let .const declName _ := type.getAppFn | return false
  return goal.casesTypes.isEagerSplit declName

private def applyCases? (goal : Goal) (fvarId : FVarId) : GrindM (Option (List Goal)) := goal.mvarId.withContext do
  let type ← whnfD (← fvarId.getType)
  if isEagerCasesCandidate goal type then
    if let .const declName _ := type.getAppFn then
      saveCases declName true
    let mvarIds ← cases goal.mvarId (mkFVar fvarId)
    return mvarIds.map fun mvarId => { goal with mvarId }
  else
    return none

private def applyInjection? (goal : Goal) (fvarId : FVarId) : MetaM (Option Goal) := do
  if let some mvarId ← injection? goal.mvarId fvarId then
    return some { goal with mvarId }
  else
    return none

/-- Introduce new hypotheses (and apply `by_contra`) until goal is of the form `... ⊢ False` -/
partial def intros  (generation : Nat) : GrindTactic' := fun goal => do
  let rec go (goal : Goal) : StateRefT (Array Goal) GrindM Unit := do
    if goal.inconsistent then
      return ()
    match (← introNext goal generation) with
    | .done =>
      if let some mvarId ← goal.mvarId.byContra? then
        go { goal with mvarId }
      else
        modify fun s => s.push goal
    | .newHyp fvarId goal =>
      if let some goals ← applyCases? goal fvarId then
        goals.forM go
      else if let some goal ← applyInjection? goal fvarId then
        go goal
      else
        go (← GoalM.run' goal <| addHypothesis fvarId generation)
    | .newDepHyp goal =>
      go goal
    | .newLocal fvarId goal =>
      if let some goals ← applyCases? goal fvarId then
        goals.forM go
      else
        go goal
  let (_, goals) ← (go goal).run #[]
  return goals.toList

/-- Asserts a new fact `prop` with proof `proof` to the given `goal`. -/
def assertAt (proof : Expr) (prop : Expr) (generation : Nat) : GrindTactic' := fun goal => do
  if isEagerCasesCandidate goal prop then
    let mvarId ← goal.mvarId.assert (← mkFreshUserName `h) prop proof
    let goal := { goal with mvarId }
    intros generation goal
  else
    let goal ← GoalM.run' goal do
      let r ← preprocess prop
      let prop' := r.expr
      let proof' ← mkEqMP (← r.getProof) proof
      add prop' proof' generation
    if goal.inconsistent then return [] else return [goal]

/-- Asserts next fact in the `goal` fact queue. -/
def assertNext : GrindTactic := fun goal => do
  let some (fact, newFacts) := goal.newFacts.dequeue?
    | return none
  assertAt fact.proof fact.prop fact.generation { goal with newFacts }

/-- Asserts all facts in the `goal` fact queue. -/
partial def assertAll : GrindTactic :=
  assertNext.iterate

end Lean.Meta.Grind
