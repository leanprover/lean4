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

/-- Returns `some c` if the given ring has a nonzero characteristic `c`. -/
def nonzeroChar? (ringId : Nat) : GoalM (Option Nat) := do
  let ring ← getRing ringId
  if let some (_, c) := ring.charInst? then
    if c != 0 then
      return some c
  return none

/-- Returns `some (charInst, c)` if the given ring has a nonzero characteristic `c`. -/
def nonzeroCharInst? (ringId : Nat) : GoalM (Option (Expr × Nat)) := do
  let ring ← getRing ringId
  if let some (inst, c) := ring.charInst? then
    if c != 0 then
      return some (inst, c)
  return none

/-- Returns `true` if the ring has a `IsCharP` instance. -/
def hasChar (ringId : Nat) : GoalM Bool := do
  return (← getRing ringId).charInst?.isSome

/--
Returns the pair `(charInst, c)`. If the ring does not have a `IsCharP` instance, then throws internal error.
-/
def getCharInst (ringId : Nat) : GoalM (Expr × Nat) := do
  let some c := (← getRing ringId).charInst?
    | throwError "`grind` internal error, ring does not have a characteristic"
  return c

/--
Converts the given ring expression into a multivariate polynomial.
If the ring has a nonzero characteristic, it is used during normalization.
-/
def toPoly (ringId : Nat) (e : RingExpr) : GoalM Poly := do
  if let some c ← nonzeroChar? ringId then
    return e.toPolyC c
  else
    return e.toPoly

end Lean.Meta.Grind.Arith.CommRing
