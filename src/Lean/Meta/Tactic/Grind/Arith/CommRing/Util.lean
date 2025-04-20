/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

namespace Lean.Meta.Grind.Arith.CommRing

def get' : GoalM State := do
  return (← get).arith.ring

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.ring := f s.arith.ring }

def getRing (ringId : Nat) : GoalM Ring := do
  let s ← get'
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

@[inline] def modifyRing (ringId : Nat) (f : Ring → Ring) : GoalM Unit := do
  modify' fun s => { s with rings := s.rings.modify ringId f }

def getTermRingId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToRingId.find? { expr := e }

def setTermRingId (e : Expr) (ringId : Nat) : GoalM Unit := do
  if let some ringId' ← getTermRingId? e then
    unless ringId' == ringId do
      reportIssue! "expression in two different rings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToRingId := s.exprToRingId.insert { expr := e } ringId }

/--
Converts the given ring expression into a multivariate polynomial.
If the ring has a nonzero characteristic, it is used during normalization.
-/
def toPoly (e : RingExpr) (ringId : Nat) : GoalM Poly := do
  let ring ← getRing ringId
  if let some (_, c) := ring.charInst? then
    if c != 0 then
      return e.toPolyC c
  return e.toPoly

/--
Returns a context of type `RArray α` containing the variables of the given ring.
`α` is the type of the ring.
-/
def toContextExpr (ringId : Nat) : GoalM Expr := do
  let ring ← getRing ringId
  if h : 0 < ring.vars.size then
    RArray.toExpr ring.type id (RArray.ofFn (ring.vars[·]) h)
  else
    RArray.toExpr ring.type id (RArray.leaf (mkApp ring.natCastFn (toExpr 0)))

end Lean.Meta.Grind.Arith.CommRing
