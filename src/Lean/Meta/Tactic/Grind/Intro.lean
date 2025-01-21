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
import Lean.Meta.Tactic.Grind.Injection
import Lean.Meta.Tactic.Grind.Core

namespace Lean.Meta.Grind

private inductive IntroResult where
  | done
  | newHyp (fvarId : FVarId) (goal : Goal)
  | newDepHyp (goal : Goal)
  | newLocal (fvarId : FVarId) (goal : Goal)
  deriving Inhabited

private def introNext (goal : Goal) : GrindM IntroResult := do
  let target ← goal.mvarId.getType
  if target.isArrow then
    goal.mvarId.withContext do
      let p := target.bindingDomain!
      if !(← isProp p) then
        let (fvarId, mvarId) ← goal.mvarId.intro1P
        return .newLocal fvarId { goal with mvarId }
      else
        let tag ← goal.mvarId.getTag
        let q := target.bindingBody!
        -- TODO: keep applying simp/eraseIrrelevantMData/canon/shareCommon until no progress
        let r ← simp p
        let fvarId ← mkFreshFVarId
        let lctx := (← getLCtx).mkLocalDecl fvarId target.bindingName! r.expr target.bindingInfo!
        let mvarNew ← mkFreshExprMVarAt lctx (← getLocalInstances) q .syntheticOpaque tag
        let mvarIdNew := mvarNew.mvarId!
        mvarIdNew.withContext do
          let h ← mkLambdaFVars #[mkFVar fvarId] mvarNew
          match r.proof? with
          | some he =>
            let hNew := mkAppN (mkConst ``Lean.Grind.intro_with_eq) #[p, r.expr, q, he, h]
            goal.mvarId.assign hNew
            return .newHyp fvarId { goal with mvarId := mvarIdNew }
          | none =>
            -- `p` and `p'` are definitionally equal
            goal.mvarId.assign h
            return .newHyp fvarId { goal with mvarId := mvarIdNew }
  else if target.isLet || target.isForall then
    let (fvarId, mvarId) ← goal.mvarId.intro1P
    mvarId.withContext do
      let localDecl ← fvarId.getDecl
      if (← isProp localDecl.type) then
        -- Add a non-dependent copy
        let mvarId ← mvarId.assert (← mkFreshUserName localDecl.userName) localDecl.type (mkFVar fvarId)
        return .newDepHyp { goal with mvarId }
      else
        return .newLocal fvarId { goal with mvarId }
  else
    return .done

private def isCasesCandidate (fvarId : FVarId) : MetaM Bool := do
  let .const declName _ := (← fvarId.getType).getAppFn | return false
  isGrindCasesTarget declName

private def applyCases? (goal : Goal) (fvarId : FVarId) : MetaM (Option (List Goal)) := goal.mvarId.withContext do
  if (← isCasesCandidate fvarId) then
    let mvarIds ← cases goal.mvarId fvarId
    return mvarIds.map fun mvarId => { goal with mvarId }
  else
    return none

private def applyInjection? (goal : Goal) (fvarId : FVarId) : MetaM (Option Goal) := do
  if let some mvarId ← injection? goal.mvarId fvarId then
    return some { goal with mvarId }
  else
    return none

/-- Introduce new hypotheses (and apply `by_contra`) until goal is of the form `... ⊢ False` -/
partial def intros (goal : Goal) (generation : Nat) : GrindM (List Goal) := do
  let rec go (goal : Goal) : StateRefT (Array Goal) GrindM Unit := do
    if goal.inconsistent then
      return ()
    match (← introNext goal) with
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
def assertAt (goal : Goal) (proof : Expr) (prop : Expr) (generation : Nat) : GrindM (List Goal) := do
  -- TODO: check whether `prop` may benefit from `intros` or not. If not, we should avoid the `assert`+`intros` step and use `Grind.add`
  let mvarId ← goal.mvarId.assert (← mkFreshUserName `h) prop proof
  let goal := { goal with mvarId }
  intros goal generation

/-- Asserts next fact in the `goal` fact queue. -/
def assertNext? (goal : Goal) : GrindM (Option (List Goal)) := do
  let some (fact, newFacts) := goal.newFacts.dequeue?
    | return none
  assertAt { goal with newFacts } fact.proof fact.prop fact.generation

partial def iterate (goal : Goal) (f : Goal → GrindM (Option (List Goal))) : GrindM (List Goal) := do
  go [goal] []
where
  go (todo : List Goal) (result : List Goal) : GrindM (List Goal) := do
    match todo with
    | [] => return result
    | goal :: todo =>
      if let some goalsNew ← f goal then
        go (goalsNew ++ todo) result
      else
        go todo (goal :: result)

/-- Asserts all facts in the `goal` fact queue. -/
partial def assertAll (goal : Goal) : GrindM (List Goal) := do
  iterate goal assertNext?

end Lean.Meta.Grind
