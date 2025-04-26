/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly

namespace Lean.Meta.Grind.Arith.CommRing

def get' : GoalM State := do
  return (← get).arith.ring

@[inline] def modify' (f : State → State) : GoalM Unit := do
  modify fun s => { s with arith.ring := f s.arith.ring }

/-- We don't want to keep carrying the `RingId` around. -/
abbrev RingM := ReaderT Nat GoalM

abbrev RingM.run (ringId : Nat) (x : RingM α) : GoalM α :=
  x ringId

abbrev getRingId : RingM Nat :=
  read

def getRing : RingM Ring := do
  let s ← get'
  let ringId ← getRingId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "`grind` internal error, invalid ringId"

@[inline] def modifyRing (f : Ring → Ring) : RingM Unit := do
  let ringId ← getRingId
  modify' fun s => { s with rings := s.rings.modify ringId f }

def getTermRingId? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToRingId.find? { expr := e }

def setTermRingId (e : Expr) : RingM Unit := do
  let ringId ← getRingId
  if let some ringId' ← getTermRingId? e then
    unless ringId' == ringId do
      reportIssue! "expression in two different rings{indentExpr e}"
    return ()
  modify' fun s => { s with exprToRingId := s.exprToRingId.insert { expr := e } ringId }

/-- Returns `some c` if the current ring has a nonzero characteristic `c`. -/
def nonzeroChar? : RingM (Option Nat) := do
  if let some (_, c) := (← getRing).charInst? then
    if c != 0 then
      return some c
  return none

/-- Returns `some (charInst, c)` if the current ring has a nonzero characteristic `c`. -/
def nonzeroCharInst? : RingM (Option (Expr × Nat)) := do
  if let some (inst, c) := (← getRing).charInst? then
    if c != 0 then
      return some (inst, c)
  return none

def noZeroDivisorsInst? : RingM (Option Expr) := do
  return (← getRing).noZeroDivInst?

/--
Returns `true` if the current ring satifies the property
```
∀ (k : Nat) (a : α), k ≠ 0 → OfNat.ofNat (α := α) k * a = 0 → a = 0
```
-/
def noZeroDivisors : RingM Bool := do
  return (← getRing).noZeroDivInst?.isSome

/-- Returns `true` if the current ring has a `IsCharP` instance. -/
def hasChar  : RingM Bool := do
  return (← getRing).charInst?.isSome

/--
Returns the pair `(charInst, c)`. If the ring does not have a `IsCharP` instance, then throws internal error.
-/
def getCharInst : RingM (Expr × Nat) := do
  let some c := (← getRing).charInst?
    | throwError "`grind` internal error, ring does not have a characteristic"
  return c

/--
Converts the given ring expression into a multivariate polynomial.
If the ring has a nonzero characteristic, it is used during normalization.
-/
def _root_.Lean.Grind.CommRing.Expr.toPolyM (e : RingExpr) : RingM Poly := do
  if let some c ← nonzeroChar? then return e.toPolyC c else return e.toPoly

def _root_.Lean.Grind.CommRing.Poly.mulConstM (p : Poly) (k : Int) : RingM Poly :=
  return p.mulConst' k (← nonzeroChar?)

def _root_.Lean.Grind.CommRing.Poly.mulMonM (p : Poly) (k : Int) (m : Mon) : RingM Poly :=
  return p.mulMon' k m (← nonzeroChar?)

def _root_.Lean.Grind.CommRing.Poly.mulM (p₁ p₂ : Poly) : RingM Poly := do
  if let some c ← nonzeroChar? then return p₁.mulC p₂ c else return p₁.mul p₂

def _root_.Lean.Grind.CommRing.Poly.combineM (p₁ p₂ : Poly) : RingM Poly :=
  return p₁.combine' p₂ (← nonzeroChar?)

end Lean.Meta.Grind.Arith.CommRing
