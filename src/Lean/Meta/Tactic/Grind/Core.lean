/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Inv
import Lean.Meta.Tactic.Grind.PP
import Lean.Meta.Tactic.Grind.Ctor
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Beta
import Lean.Meta.Tactic.Grind.Internalize
import Lean.Meta.Tactic.Grind.Simp

namespace Lean.Meta.Grind

/--
The fields `target?` and `proof?` in `e`'s `ENode` are encoding a transitivity proof
from `e` to the root of the equivalence class
This method "inverts" the proof, and makes it to go from the root of the equivalence class to `e`.

We use this method when merging two equivalence classes.
-/
private partial def invertTrans (e : Expr) : GoalM Unit := do
  go e false none none
where
  go (e : Expr) (flippedNew : Bool) (targetNew? : Option Expr) (proofNew? : Option Expr) : GoalM Unit := do
    let node ← getENode e
    if let some target := node.target? then
      go target (!node.flipped) (some e) node.proof?
    setENode e { node with
      target? := targetNew?
      flipped := flippedNew
      proof?  := proofNew?
    }

/--
Remove `root` parents from the congruence table.
This is an auxiliary function performed while merging equivalence classes.
-/
private def removeParents (root : Expr) : GoalM ParentSet := do
  let parents ← getParents root
  for parent in parents do
    -- Recall that we may have `Expr.forallE` in `parents` because of `ForallProp.lean`
    if (← pure parent.isApp <&&> isCongrRoot parent) then
      trace_goal[grind.debug.parent] "remove: {parent}"
      modify fun s => { s with congrTable := s.congrTable.erase { e := parent } }
  return parents

/--
Reinsert parents into the congruence table and detect new equalities.
This is an auxiliary function performed while merging equivalence classes.
-/
private def reinsertParents (parents : ParentSet) : GoalM Unit := do
  for parent in parents do
    if (← pure parent.isApp <&&> isCongrRoot parent) then
      trace_goal[grind.debug.parent] "reinsert: {parent}"
      addCongrTable parent

/-- Closes the goal when `True` and `False` are in the same equivalence class. -/
private def closeGoalWithTrueEqFalse : GoalM Unit := do
  let mvarId := (← get).mvarId
  unless (← mvarId.isAssigned) do
    let trueEqFalse ← mkEqFalseProof (← getTrueExpr)
    let falseProof ← mkEqMP trueEqFalse (mkConst ``True.intro)
    closeGoal falseProof

/-- Closes the goal when `lhs` and `rhs` are both literal values and belong to the same equivalence class. -/
private def closeGoalWithValuesEq (lhs rhs : Expr) : GoalM Unit := do
  let p ← mkEq lhs rhs
  let hp ← mkEqProof lhs rhs
  let d ← mkDecide p
  let pEqFalse := mkApp3 (mkConst ``eq_false_of_decide) p d.appArg! (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``false))
  let falseProof ← mkEqMP pEqFalse hp
  closeGoal falseProof

/--
Updates the modification time to `gmt` for the parents of `root`.
The modification time is used to decide which terms are considered during e-matching.
-/
private partial def updateMT (root : Expr) : GoalM Unit := do
  let gmt := (← get).gmt
  for parent in (← getParents root) do
    let node ← getENode parent
    if node.mt < gmt then
      setENode parent { node with mt := gmt }
      updateMT parent

/--
Helper function for combining `ENode.offset?` fields and propagating an equality
to the offset constraint module.
-/
private def propagateOffsetEq (rhsRoot lhsRoot : ENode) : GoalM Unit := do
  match lhsRoot.offset? with
  | some lhsOffset =>
    if let some rhsOffset := rhsRoot.offset? then
      Arith.processNewOffsetEq lhsOffset rhsOffset
    else if isNatNum rhsRoot.self then
      Arith.processNewOffsetEqLit lhsOffset rhsRoot.self
    else
      -- We have to retrieve the node because other fields have been updated
      let rhsRoot ← getENode rhsRoot.self
      setENode rhsRoot.self { rhsRoot with offset? := lhsOffset }
  | none =>
    if isNatNum lhsRoot.self then
    if let some rhsOffset := rhsRoot.offset? then
      Arith.processNewOffsetEqLit rhsOffset lhsRoot.self

/--
Tries to apply beta-reductiong using the parent applications of the functions in `fns` with
the lambda expressions in `lams`.
-/
def propagateBeta (lams : Array Expr) (fns : Array Expr) : GoalM Unit := do
  if lams.isEmpty then return ()
  let lamRoot ← getRoot lams.back!
  trace_goal[grind.debug.beta] "fns: {fns}, lams: {lams}"
  for fn in fns do
    trace_goal[grind.debug.beta] "fn: {fn}, parents: {(← getParents fn).toArray}"
    for parent in (← getParents fn) do
      let mut args := #[]
      let mut curr := parent
      trace_goal[grind.debug.beta] "parent: {parent}"
      repeat
        trace_goal[grind.debug.beta] "curr: {curr}"
        if (← isEqv curr lamRoot) then
          propagateBetaEqs lams curr args.reverse
        let .app f arg := curr
          | break
        -- Remark: recall that we do not eagerly internalize partial applications.
        internalize curr (← getGeneration parent)
        args := args.push arg
        curr := f

private partial def addEqStep (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  let lhsNode ← getENode lhs
  let rhsNode ← getENode rhs
  if isSameExpr lhsNode.root rhsNode.root then
    -- `lhs` and `rhs` are already in the same equivalence class.
    trace_goal[grind.debug] "{← ppENodeRef lhs} and {← ppENodeRef rhs} are already in the same equivalence class"
    return ()
  trace_goal[grind.eqc] "{← if isHEq then mkHEq lhs rhs else mkEq lhs rhs}"
  let lhsRoot ← getENode lhsNode.root
  let rhsRoot ← getENode rhsNode.root
  let mut valueInconsistency := false
  let mut trueEqFalse := false
  if lhsRoot.interpreted && rhsRoot.interpreted then
    if lhsNode.root.isTrue || rhsNode.root.isTrue then
      markAsInconsistent
      trueEqFalse := true
    else
      valueInconsistency := true
  if    (lhsRoot.interpreted && !rhsRoot.interpreted)
     || (lhsRoot.ctor && !rhsRoot.ctor)
     || (lhsRoot.size > rhsRoot.size && !rhsRoot.interpreted && !rhsRoot.ctor) then
    go rhs lhs rhsNode lhsNode rhsRoot lhsRoot true
  else
    go lhs rhs lhsNode rhsNode lhsRoot rhsRoot false
  if trueEqFalse then
    closeGoalWithTrueEqFalse
  unless (← isInconsistent) do
    if lhsRoot.ctor && rhsRoot.ctor then
      propagateCtor lhsRoot.self rhsRoot.self
  unless (← isInconsistent) do
    if valueInconsistency then
      closeGoalWithValuesEq lhsRoot.self rhsRoot.self
  trace_goal[grind.debug] "after addEqStep, {← (← get).ppState}"
  checkInvariants
where
  go (lhs rhs : Expr) (lhsNode rhsNode lhsRoot rhsRoot : ENode) (flipped : Bool) : GoalM Unit := do
    trace_goal[grind.debug] "adding {← ppENodeRef lhs} ↦ {← ppENodeRef rhs}"
    /-
    We have the following `target?/proof?`
    `lhs -> ... -> lhsNode.root`
    `rhs -> ... -> rhsNode.root`
    We want to convert it to
    `lhsNode.root -> ... -> lhs -*-> rhs -> ... -> rhsNode.root`
    where step `-*->` is justified by `proof` (or `proof.symm` if `flipped := true`)
    -/
    invertTrans lhs
    setENode lhs { lhsNode with
      target? := rhs
      proof?  := proof
      flipped
    }
    let lams₁ ← getEqcLambdas lhsRoot
    let lams₂ ← getEqcLambdas rhsRoot
    let fns₁  ← if lams₁.isEmpty then pure #[] else getFnRoots rhsRoot.self
    let fns₂  ← if lams₂.isEmpty then pure #[] else getFnRoots lhsRoot.self
    let parents ← removeParents lhsRoot.self
    updateRoots lhs rhsNode.root
    trace_goal[grind.debug] "{← ppENodeRef lhs} new root {← ppENodeRef rhsNode.root}, {← ppENodeRef (← getRoot lhs)}"
    reinsertParents parents
    propagateEqcDown lhs
    setENode lhsNode.root { (← getENode lhsRoot.self) with -- We must retrieve `lhsRoot` since it was updated.
      next := rhsRoot.next
    }
    setENode rhsNode.root { rhsRoot with
      next       := lhsRoot.next
      size       := rhsRoot.size + lhsRoot.size
      hasLambdas := rhsRoot.hasLambdas || lhsRoot.hasLambdas
      heqProofs  := isHEq || rhsRoot.heqProofs || lhsRoot.heqProofs
    }
    propagateBeta lams₁ fns₁
    propagateBeta lams₂ fns₂
    resetParentsOf lhsRoot.self
    copyParentsTo parents rhsNode.root
    unless (← isInconsistent) do
      updateMT rhsRoot.self
    propagateOffsetEq rhsRoot lhsRoot
    unless (← isInconsistent) do
      for parent in parents do
        propagateUp parent

  updateRoots (lhs : Expr) (rootNew : Expr) : GoalM Unit := do
    traverseEqc lhs fun n =>
      setENode n.self { n with root := rootNew }

  propagateEqcDown (lhs : Expr) : GoalM Unit := do
    traverseEqc lhs fun n =>
      unless (← isInconsistent) do
        propagateDown n.self

/-- Ensures collection of equations to be processed is empty. -/
private def resetNewEqs : GoalM Unit :=
  modify fun s => { s with newEqs := #[] }

/-- Pops and returns the next equality to be processed. -/
private def popNextEq? : GoalM (Option NewEq) := do
  let r := (← get).newEqs.back?
  if r.isSome then
    modify fun s => { s with newEqs := s.newEqs.pop }
  return r

private def processNewEqs : GoalM Unit := do
  repeat
    if (← isInconsistent) then
      resetNewEqs
      return ()
    checkSystem "grind"
    let some { lhs, rhs, proof, isHEq } := (← popNextEq?)
      | return ()
    addEqStep lhs rhs proof isHEq

private def addEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  addEqStep lhs rhs proof isHEq
  processNewEqs

/-- Adds a new equality `lhs = rhs`. It assumes `lhs` and `rhs` have already been internalized. -/
private def addEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof false

/-- Adds a new heterogeneous equality `HEq lhs rhs`. It assumes `lhs` and `rhs` have already been internalized. -/
private def addHEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof true

/-- Save asserted facts for pretty printing goal. -/
private def storeFact (fact : Expr) : GoalM Unit := do
  modify fun s => { s with facts := s.facts.push fact }

/-- Internalizes `lhs` and `rhs`, and then adds equality `lhs = rhs`. -/
def addNewEq (lhs rhs proof : Expr) (generation : Nat) : GoalM Unit := do
  let eq ← mkEq lhs rhs
  storeFact eq
  internalize lhs generation eq
  internalize rhs generation eq
  addEq lhs rhs proof

/-- Adds a new `fact` justified by the given proof and using the given generation. -/
def add (fact : Expr) (proof : Expr) (generation := 0) : GoalM Unit := do
  if fact.isTrue then return ()
  storeFact fact
  trace_goal[grind.assert] "{fact}"
  if (← isInconsistent) then return ()
  resetNewEqs
  let_expr Not p := fact
    | go fact false
  go p true
where
  go (p : Expr) (isNeg : Bool) : GoalM Unit := do
    match_expr p with
    | Eq α lhs rhs =>
      if α.isProp then
        -- It is morally an iff.
        -- We do not use the `goEq` optimization because we want to register `p` as a case-split
        goFact p isNeg
      else
        goEq p lhs rhs isNeg false
    | HEq _ lhs _ rhs => goEq p lhs rhs isNeg true
    | _ => goFact p isNeg

  goFact (p : Expr) (isNeg : Bool) : GoalM Unit := do
    internalize p generation
    if isNeg then
      addEq p (← getFalseExpr) (← mkEqFalse proof)
    else
      addEq p (← getTrueExpr) (← mkEqTrue proof)

  goEq (p : Expr) (lhs rhs : Expr) (isNeg : Bool) (isHEq : Bool) : GoalM Unit := do
    if isNeg then
      internalize p generation
      addEq p (← getFalseExpr) (← mkEqFalse proof)
    else
      internalize lhs generation p
      internalize rhs generation p
      addEqCore lhs rhs proof isHEq

/-- Adds a new hypothesis. -/
def addHypothesis (fvarId : FVarId) (generation := 0) : GoalM Unit := do
  add (← fvarId.getType) (mkFVar fvarId) generation

/--
Helper function for executing `x` with a fresh `newEqs` and without modifying
the goal state.
 -/
private def withoutModifyingState (x : GoalM α) : GoalM α := do
  let saved ← get
  modify fun goal => { goal with newEqs := {} }
  try
    x
  finally
    set saved

/--
If `e` has not been internalized yet, simplify it, and internalize the result.
-/
private def simpAndInternalize (e : Expr) (gen : Nat := 0) : GoalM Simp.Result := do
  if (← alreadyInternalized e) then
    return { expr := e }
  else
    let r ← simp e
    internalize r.expr gen
    return r

/--
Try to construct a proof that `lhs = rhs` using the information in the
goal state. If `lhs` and `rhs` have not been internalized, this function
will internalize then, process propagated equalities, and then check
whether they are in the same equivalence class or not.
The goal state is not modified by this function.
This function mainly relies on congruence closure, and constraint
propagation. It will not perform case analysis.
-/
def proveEq? (lhs rhs : Expr) : GoalM (Option Expr) := do
  if (← alreadyInternalized lhs <&&> alreadyInternalized rhs) then
    if (← isEqv lhs rhs) then
      return some (← mkEqProof lhs rhs)
    else
      return none
  else withoutModifyingState do
    let lhs ← simpAndInternalize lhs
    let rhs ← simpAndInternalize rhs
    processNewEqs
    unless (← isEqv lhs.expr rhs.expr) do return none
    unless (← hasSameType lhs.expr rhs.expr) do return none
    let h ← mkEqProof lhs.expr rhs.expr
    let h ← match lhs.proof?, rhs.proof? with
      | none,    none    => pure h
      | none,    some h₂ => mkEqTrans h (← mkEqSymm h₂)
      | some h₁, none    => mkEqTrans h₁ h
      | some h₁, some h₂ => mkEqTrans (← mkEqTrans h₁ h) (← mkEqSymm h₂)
    return some h

end Lean.Meta.Grind
