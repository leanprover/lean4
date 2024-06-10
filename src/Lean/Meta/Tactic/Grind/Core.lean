/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.LitValues

namespace Lean.Meta.Grind
/--
Returns `true` if `e` is `True`, `False`, or a literal value.
See `LitValues` for supported literals.
-/
def isInterpreted (e : Expr) : MetaM Bool := do
  if e.isTrue || e.isFalse then return true
  isLitValue e

/--
Creates an `ENode` for `e` if one does not already exist.
This method assumes `e` has been hashconsed.
-/
def mkENode (e : Expr) (generation : Nat := 0) : GoalM Unit := do
  if (← getENode? e).isSome then return ()
  let ctor := (← isConstructorAppCore? e).isSome
  let interpreted ← isInterpreted e
  mkENodeCore e interpreted ctor generation

/--
Returns the root element in the equivalence class of `e`.
-/
def getRoot (e : Expr) : GoalM Expr := do
  let some n ← getENode? e | return e
  return n.root

/--
Returns the next element in the equivalence class of `e`.
-/
def getNext (e : Expr) : GoalM Expr := do
  let some n ← getENode? e | return e
  return n.next

@[inline] def isSameExpr (a b : Expr) : Bool :=
  -- It is safe to use pointer equality because we hashcons all expressions
  -- inserted into the E-graph
  unsafe ptrEq a b

private def pushNewEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit :=
  modify fun s => { s with newEqs := s.newEqs.push { lhs, rhs, proof, isHEq } }

@[inline] private def pushNewEq (lhs rhs proof : Expr) : GoalM Unit :=
  pushNewEqCore lhs rhs proof (isHEq := false)

@[inline] private def pushNewHEq (lhs rhs proof : Expr) : GoalM Unit :=
  pushNewEqCore lhs rhs proof (isHEq := true)

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
    let some node ← getENode? e | unreachable!
    if let some target := node.target? then
      go target (!node.flipped) (some e) node.proof?
    setENode e { node with
      target? := targetNew?
      flipped := flippedNew
      proof?  := proofNew?
    }

private def markAsInconsistent : GoalM Unit :=
  modify fun s => { s with inconsistent := true }

private partial def addEqStep (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  let some lhsNode ← getENode? lhs | return () -- `lhs` has not been internalized yet
  let some rhsNode ← getENode? rhs | return () -- `rhs` has not been internalized yet
  if isSameExpr lhsNode.root rhsNode.root then return () -- `lhs` and `rhs` are already in the same equivalence class.
  let some lhsRoot ← getENode? lhsNode.root | unreachable!
  let some rhsRoot ← getENode? rhsNode.root | unreachable!
  if    (lhsRoot.interpreted && !rhsRoot.interpreted)
     || (lhsRoot.ctor && !rhsRoot.ctor)
     || (lhsRoot.size > rhsRoot.size && !rhsRoot.interpreted && !rhsRoot.ctor) then
    go rhs lhs rhsNode lhsNode rhsRoot lhsRoot true
  else
    go lhs rhs lhsNode rhsNode lhsRoot rhsRoot false
where
  go (lhs rhs : Expr) (lhsNode rhsNode lhsRoot rhsRoot : ENode) (flipped : Bool) : GoalM Unit := do
    let mut valueInconsistency := false
    if lhsRoot.interpreted && rhsRoot.interpreted then
      if lhsNode.root.isTrue || rhsNode.root.isTrue then
        markAsInconsistent
      else
        valueInconsistency := true
    -- TODO: process valueInconsistency := true
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
    -- TODO: Remove parents from congruence table
    -- TODO: set propagateBool
    updateRoots lhs rhsNode.root true -- TODO
    -- TODO: Reinsert parents into congruence table
    setENode lhsNode.root { lhsRoot with
      next := rhsRoot.next
    }
    setENode rhsNode.root { rhsRoot with
      next := lhsRoot.next
      size := rhsRoot.size + lhsRoot.size
      hasLambdas := rhsRoot.hasLambdas || lhsRoot.hasLambdas
      heqProofs  := isHEq || rhsRoot.heqProofs || lhsRoot.heqProofs
    }
    -- TODO: copy parentst from lhsRoot parents to rhsRoot parents

  updateRoots (lhs : Expr) (rootNew : Expr) (_propagateBool : Bool) : GoalM Unit := do
    let rec loop (e : Expr) : GoalM Unit := do
      -- TODO: propagateBool
      let some n ← getENode? e | unreachable!
      setENode e { n with root := rootNew }
      if isSameExpr lhs n.next then return ()
      loop n.next
    loop lhs

partial def addEqCore (lhs rhs proof : Expr) (isHEq : Bool) : GoalM Unit := do
  addEqStep lhs rhs proof isHEq
  processTodo
where
  processTodo : GoalM Unit := do
    if (← get).inconsistent then
      modify fun s => { s with newEqs := #[] }
      return ()
    let some { lhs, rhs, proof, isHEq } := (← get).newEqs.back? | return ()
    addEqStep lhs rhs proof isHEq
    processTodo

def addEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof false

def addHEq (lhs rhs proof : Expr) : GoalM Unit := do
  addEqCore lhs rhs proof true

end Lean.Meta.Grind
