/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Lemmas
public import Lean.Meta.Tactic.Grind.Action
import Lean.Meta.Tactic.Apply
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.CasesMatch
import Lean.Meta.Tactic.Grind.Injection
import Lean.Meta.Tactic.Grind.Core
import Lean.Meta.Tactic.Grind.RevertAll
public section
namespace Lean.Meta.Grind

private inductive IntroResult where
  | done (goal : Goal)
  | newHyp (fvarId : FVarId) (goal : Goal)
  | newDepHyp (goal : Goal)
  | newLocal (fvarId : FVarId) (goal : Goal)
  deriving Inhabited

/--
Returns `true` if `e` is marked with the `alreadyNorm` gadget.
See `alreadyNorm` documentation for additional details
-/
private def isAlreadyNorm? (e : Expr) : Option Expr :=
  let_expr Lean.Grind.alreadyNorm c := e | none
  some c

/--
Similar to `Grind.preprocess`, but does not simplify `e` if
`isMatchCondCandidate` (aka `Simp.isEqnThmHypothesis`) is `true`.
We added this feature because it may be coming from external sources
(e.g., manually applying an function induction principle before invoking `grind`).
-/
def preprocessHypothesis (e : Expr) : GoalM Simp.Result := do
  if isMatchCondCandidate e then
    preprocess (markAsPreMatchCond e)
  else if let some c := isAlreadyNorm? e then
    let c ← shareCommon (← canon c)
    return { expr := c }
  else
    preprocess e

/--
Helper function for `mkCleanName`.
It ensures base name is a simple `Name` and does not have a `_<idx>` suffix
-/
private def mkBaseName (name : Name) (type : Expr) : MetaM Name := do
  if let .str _ s := name then
    let pos := s.find '_'
    if h : pos.IsAtEnd then
      return Name.mkSimple s
    else
      let suffix := s.sliceFrom (pos.next h)
      unless suffix.isNat do
        return Name.mkSimple s
      let s := s.sliceTo pos
      unless s.isEmpty do
        return Name.mkSimple s.copy
  if (← isProp type) then return `h else return `x

private def mkCleanName (name : Name) (type : Expr) : GoalM Name := do
  if (← getConfig).clean then
    let mut name := name
    if name.hasMacroScopes then
      name := name.eraseMacroScopes
      if name == `x || name == `a then
        if (← isProp type) then
          name := `h
    if (← get).clean.used.contains name then
      let base ← mkBaseName name type
      let mut i := if let some i := (← get).clean.next.find? base then i else 1
      repeat
        name := base.appendIndexAfter i
        i := i + 1
        unless (← get).clean.used.contains name do
          break
      modify fun s => { s with clean.next := s.clean.next.insert base i }
    modify fun s => { s with clean.used := s.clean.used.insert name }
    return name
  else if let some originalName := getOriginalName? name then
    return originalName
  else if name.hasMacroScopes then
    let name' := name.eraseMacroScopes
    if name' == `x || name' == `a then
      if (← isProp type) then
        return (← mkFreshUserName `h)
    return name
  else
    mkFreshUserName name

private def intro1 : GoalM FVarId := do
  let target ← (← get).mvarId.getType
  let (name, type) ← match target with
    | .forallE n d .. => pure (n, d)
    | .letE n d .. => pure (n, d)
    | _ => throwError "`grind` internal error, binder expected"
  let name ← mkCleanName name type
  let (fvarId, mvarId) ← (← get).mvarId.intro name
  modify fun s => { s with mvarId }
  return fvarId

private partial def introNext (goal : Goal) (generation : Nat) : GrindM IntroResult := do
  Prod.fst <$> GoalM.run goal do
    let target ← (← get).mvarId.getType
    if target.isForall then
      let p := target.bindingDomain!
      if !(← isProp p) then
        let fvarId ← intro1
        return .newLocal fvarId (← get)
      else
        let mvarId := (← get).mvarId
        let tag ← mvarId.getTag
        let qBase := target.bindingBody!
        let fvarId ← mkFreshFVarId
        let fvar := mkFVar fvarId
        let r ← preprocessHypothesis p
        let lctx := (← getLCtx).mkLocalDecl fvarId (← mkCleanName target.bindingName! r.expr) r.expr target.bindingInfo!
        let mut localInsts ← getLocalInstances
        if let some className ← isClass? r.expr then
          localInsts := localInsts.push { className, fvar }
        match r.proof? with
        | some he =>
          if target.isArrow then
            let q := qBase
            let u ← getLevel q
            let mvarNew ← mkFreshExprMVarAt lctx localInsts q .syntheticOpaque tag
            let mvarIdNew := mvarNew.mvarId!
            mvarIdNew.withContext do
              let h ← mkLambdaFVars #[fvar] mvarNew
              let hNew := mkAppN (mkConst ``Lean.Grind.intro_with_eq [u]) #[p, r.expr, q, he, h]
              mvarId.assign hNew
              return .newHyp fvarId { (← get) with mvarId := mvarIdNew }
          else
            let q := mkLambda target.bindingName! target.bindingInfo! p qBase
            let q' := qBase.instantiate1 (mkApp4 (mkConst ``Eq.mpr_prop) p r.expr he fvar)
            let u ← getLevel q'
            let mvarNew ← mkFreshExprMVarAt lctx localInsts q' .syntheticOpaque tag
            let mvarIdNew := mvarNew.mvarId!
            mvarIdNew.withContext do
              let h ← mkLambdaFVars #[fvar] mvarNew
              let hNew := mkAppN (mkConst ``Lean.Grind.intro_with_eq' [u]) #[p, r.expr, q, he, h]
              mvarId.assign hNew
              return .newHyp fvarId { (← get) with mvarId := mvarIdNew }
        | none =>
          -- `p` and `p'` are definitionally equal
          let q := if target.isArrow then qBase else qBase.instantiate1 (mkFVar fvarId)
          let mvarNew ← mkFreshExprMVarAt lctx localInsts q .syntheticOpaque tag
          let mvarIdNew := mvarNew.mvarId!
          mvarIdNew.withContext do
            let h ← mkLambdaFVars #[mkFVar fvarId] mvarNew
            mvarId.assign h
            return .newHyp fvarId { (← get) with mvarId := mvarIdNew }
    else if target.isLet then
      if (← getConfig).zetaDelta then
        let targetNew := expandLet target #[]
        let mvarId := (← get).mvarId
        mvarId.withContext do
          let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew (← mvarId.getTag)
          mvarId.assign mvarNew
          introNext { (← get) with mvarId := mvarNew.mvarId! } generation
      else
        let fvarId ← intro1
        (← get).mvarId.withContext do
          let localDecl ← fvarId.getDecl
          if (← isProp localDecl.type) then
            -- Add a non-dependent copy
            let mvarId ← (← get).mvarId.assert (← mkCleanName `h localDecl.type) localDecl.type (mkFVar fvarId)
            return .newDepHyp { (← get) with mvarId }
          else
            let v := (← fvarId.getDecl).value
            let r ← preprocessHypothesis v
            let x ← shareCommon (mkFVar fvarId)
            addNewEq x r.expr (← r.getProof) generation
            return .newLocal fvarId (← get)
    else
      return .done goal

private def isEagerCasesCandidate (type : Expr) : GrindM Bool := do
  let .const declName _ := type.getAppFn | return false
  isEagerSplit declName

/-- Returns `true` if `type` is an inductive type with at most one constructor. -/
private def isCheapInductive (type : Expr) : CoreM Bool := do
  let .const declName _ := type.getAppFn | return false
  let .inductInfo info ← getConstInfo declName | return false
  return info.numCtors <= 1

private def applyInjection? (goal : Goal) (fvarId : FVarId) : MetaM (Option Goal) := do
  if let some mvarId ← injection? goal.mvarId fvarId then
    return some { goal with mvarId }
  else
    return none

private def exfalsoIfNotProp (goal : Goal) : MetaM Goal := goal.mvarId.withContext do
  if (← isProp (← goal.mvarId.getType)) then
    return goal
  else
    return { goal with mvarId := (← goal.mvarId.exfalso) }

def Goal.lastDecl? (goal : Goal) : MetaM (Option LocalDecl) := do
  return (← goal.mvarId.getDecl).lctx.lastDecl

namespace Action

private def applyCases? (goal : Goal) (fvarId : FVarId) (kp : ActionCont) : GrindM (Option ActionResult) := goal.withContext do
  /-
  Remark: we used to use `whnfD`. This was a mistake, we don't want to unfold user-defined abstractions.
  Example: `a ∣ b` is defined as `∃ x, b = a * x`
  -/
  let type ← whnf (← fvarId.getType)
  unless (← isEagerCasesCandidate type) do return none
  if (← cheapCasesOnly) then
    unless (← isCheapInductive type) do return none
  if let .const declName _ := type.getAppFn then
    saveCases declName
  let mvarIds ← cases goal.mvarId (mkFVar fvarId)
  let subgoals := mvarIds.map fun mvarId => { goal with mvarId }
  let mut seqNew : Array (TSyntax `grind) := #[]
  let mut stuckNew : Array Goal := #[]
  for subgoal in subgoals do
    match (← kp subgoal) with
    | .stuck gs => stuckNew := stuckNew ++ gs
    | .closed seq => seqNew := seqNew ++ seq
  if stuckNew.isEmpty then
    return some (.closed seqNew.toList)
  else
    return some (.stuck stuckNew.toList)

def intro (generation : Nat) : Action := fun goal kna kp => do
  if goal.inconsistent then return .closed []
  let target ← goal.mvarId.getType
  if target.isFalse then
    kna goal
  else match (← introNext goal generation) with
    | .done goal =>
      let goal ← exfalsoIfNotProp goal
      if let some mvarId ← goal.mvarId.byContra? then
        kp { goal with mvarId }
      else
        kp goal
    | .newDepHyp goal =>
      kp goal
    | .newLocal fvarId goal =>
      if let some result ← applyCases? goal fvarId kp then
        return result
      else
        kp goal
    | .newHyp fvarId goal =>
      if let some goal ← applyInjection? goal fvarId then
        kp goal
      else if let some result ← applyCases? goal fvarId kp then
        return result
      else
        let goal ← GoalM.run' goal <| addHypothesis fvarId generation
        kp goal

private def hugeNumber := 1000000

def intros (generation : Nat) : Action :=
  ungroup >> (intro generation).loop hugeNumber >> group

/-- Asserts a new fact `prop` with proof `proof` to the given `goal`. -/
private def assertAt (proof : Expr) (prop : Expr) (generation : Nat) : Action := fun goal kna kp => do
  if (← isEagerCasesCandidate prop) then
    let mvarId ← goal.mvarId.assert (← mkFreshUserName `h) prop proof
    intros generation { goal with mvarId } kna kp
  else goal.withContext do
    let goal ← GoalM.run' goal do
      let r ← preprocess prop
      let prop' := r.expr
      let proof' := mkApp4 (mkConst ``Eq.mp [levelZero]) prop r.expr (← r.getProof) proof
      add prop' proof' generation
    kp goal

/--
Asserts next fact in the `goal` fact queue.
Returns `true` if the queue was not empty and `false` otherwise.
-/
def assertNext : Action := fun goal kna kp => do
  if goal.inconsistent then return .closed []
  let some (fact, newRawFacts) := goal.newRawFacts.dequeue?
    | kna goal
  let goal := { goal with newRawFacts }
  withSplitSource fact.splitSource do
    assertAt fact.proof fact.prop fact.generation goal kna kp

/--
Asserts all facts in the `goal` fact queue.
Returns `true` if the queue was not empty and `false` otherwise.
-/
def assertAll : Action :=
  assertNext.loop hugeNumber

end Action

end Lean.Meta.Grind
