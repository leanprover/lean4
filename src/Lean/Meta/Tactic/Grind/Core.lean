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
import Lean.Meta.Tactic.Grind.Internalize

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
  let parents ← getParentsAndReset root
  for parent in parents do
    modify fun s => { s with congrTable := s.congrTable.erase { e := parent } }
  return parents

/--
Reinsert parents into the congruence table and detect new equalities.
This is an auxiliary function performed while merging equivalence classes.
-/
private def reinsertParents (parents : ParentSet) : GoalM Unit := do
  for parent in parents do
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

private partial def addEqStep (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  trace[grind.eq] "{lhs} {if isHEq then "≡" else "="} {rhs}"
  let lhsNode ← getENode lhs
  let rhsNode ← getENode rhs
  if isSameExpr lhsNode.root rhsNode.root then
    -- `lhs` and `rhs` are already in the same equivalence class.
    trace[grind.debug] "{← ppENodeRef lhs} and {← ppENodeRef rhs} are already in the same equivalence class"
    return ()
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
  trace[grind.debug] "after addEqStep, {← ppState}"
  checkInvariants
where
  go (lhs rhs : Expr) (lhsNode rhsNode lhsRoot rhsRoot : ENode) (flipped : Bool) : GoalM Unit := do
    trace[grind.debug] "adding {← ppENodeRef lhs} ↦ {← ppENodeRef rhs}"
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
    let parents ← removeParents lhsRoot.self
    updateRoots lhs rhsNode.root
    trace[grind.debug] "{← ppENodeRef lhs} new root {← ppENodeRef rhsNode.root}, {← ppENodeRef (← getRoot lhs)}"
    reinsertParents parents
    setENode lhsNode.root { (← getENode lhsRoot.self) with -- We must retrieve `lhsRoot` since it was updated.
      next := rhsRoot.next
    }
    setENode rhsNode.root { rhsRoot with
      next := lhsRoot.next
      size := rhsRoot.size + lhsRoot.size
      hasLambdas := rhsRoot.hasLambdas || lhsRoot.hasLambdas
      heqProofs  := isHEq || rhsRoot.heqProofs || lhsRoot.heqProofs
    }
    copyParentsTo parents rhsNode.root
    unless (← isInconsistent) do
      for parent in parents do
        propagateUp parent

  updateRoots (lhs : Expr) (rootNew : Expr) : GoalM Unit := do
    let rec loop (e : Expr) : GoalM Unit := do
      let n ← getENode e
      setENode e { n with root := rootNew }
      unless (← isInconsistent) do
        propagateDown e
      if isSameExpr lhs n.next then return ()
      loop n.next
    loop lhs

/-- Ensures collection of equations to be processed is empty. -/
private def resetNewEqs : GoalM Unit :=
  modify fun s => { s with newEqs := #[] }

/-- Pops and returns the next equality to be processed. -/
private def popNextEq? : GoalM (Option NewEq) := do
  let r := (← get).newEqs.back?
  if r.isSome then
    modify fun s => { s with newEqs := s.newEqs.pop }
  return r

private partial def addEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  addEqStep lhs rhs proof isHEq
  processTodo
where
  processTodo : GoalM Unit := do
    if (← isInconsistent) then
      resetNewEqs
      return ()
    let some { lhs, rhs, proof, isHEq } := (← popNextEq?) | return ()
    addEqStep lhs rhs proof isHEq
    processTodo

def addEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof false

def addHEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof true

/--
Adds a new `fact` justified by the given proof and using the given generation.
-/
def add (fact : Expr) (proof : Expr) (generation := 0) : GoalM Unit := do
  trace[grind.add] "{proof} : {fact}"
  if (← isInconsistent) then return ()
  resetNewEqs
  let_expr Not p := fact
    | go fact false
  go p true
where
  go (p : Expr) (isNeg : Bool) : GoalM Unit := do
    trace[grind.add] "isNeg: {isNeg}, {p}"
    match_expr p with
    | Eq _ lhs rhs => goEq p lhs rhs isNeg false
    | HEq _ lhs _ rhs => goEq p lhs rhs isNeg true
    | _ =>
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
      internalize lhs generation
      internalize rhs generation
      addEqCore lhs rhs proof isHEq

/--
Adds a new hypothesis.
-/
def addHyp (fvarId : FVarId) (generation := 0) : GoalM Unit := do
  add (← fvarId.getType) (mkFVar fvarId) generation

end Lean.Meta.Grind
