/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr

namespace Lean.Meta.Grind.Arith.Cutsat

def getBestLower? (x : Var) : GoalM (Option (Int × LeCnstr)) := do
  let s ← get'
  let mut best? := none
  for c in s.lowers[x]! do
    let .add k _ p := c.p | c.throwUnexpected
    let some v ← p.eval? | c.throwUnexpected
    let lower' := Int.Linear.cdiv v (-k)
    if let some (lower, _) := best? then
      if lower' > lower then
        best? := some (lower', c)
    else
      best? := some (lower', c)
  return best?

def getBestUpper? (x : Var) : GoalM (Option (Int × LeCnstr)) := do
  let s ← get'
  let mut best? := none
  for c in s.uppers[x]! do
    let .add k _ p := c.p | c.throwUnexpected
    let some v ← p.eval? | c.throwUnexpected
    let upper' := (-v) / k
    if let some (upper, _) := best? then
      if upper' < upper then
        best? := some (upper', c)
    else
      best? := some (upper', c)
  return best?

def getDvdSolutions? (c : DvdCnstr) : GoalM (Option (Int × Int)) := do
  let d := c.d
  let .add a _ p := c.p | c.throwUnexpected
  let some b ← p.eval? | c.throwUnexpected
  -- We must solve `d ∣ a*x + b`
  let g := d.gcd a
  if b % g != 0 then
    return none -- no solutions
  let d := d / g
  let a := a / g
  let b := b / g
  -- `α*a + β*d = 1`
  -- `α*a = 1 (mod d)`
  let (_, α, _β) := gcdExt a d
  -- `a'*a = 1 (mod d)`
  let a' := if α < 0 then α % d else α
  -- `a*x = -b (mod d)`
  -- `x = -b*a' (mod d)`
  -- `x = k*d + -b*a'` for any k
  return some (d, -b*a')

private partial def setAssignment (x : Var) (v : Int) : GoalM Unit := do
  if x == (← get').assignment.size then
    trace[grind.cutsat.assign] "{(← getVar x)} := {v}"
    modify' fun s => { s with assignment := s.assignment.push v }
  else if x > (← get').assignment.size then
    modify' fun s => { s with assignment := s.assignment.push 0 }
    setAssignment x v
  else
    throwError "`grind` internal error, variable is already assigned"

def resolveLowerUpperConflict (c₁ c₂ : LeCnstr) : GoalM Unit := do
  trace[grind.cutsat.conflict] "{← c₁.denoteExpr}, {← c₂.denoteExpr}"
  let .add a₁ _ p₁ := c₁.p | c₁.throwUnexpected
  let .add a₂ _ p₂ := c₂.p | c₂.throwUnexpected
  let p := p₁.mul a₂.natAbs |>.combine (p₂.mul a₁.natAbs)
  if (← p.satisfiedLe) == .false then
    -- If current assignment does not satisfy the real shadow, we use it even if it is not precise when
    -- `a₁.natAbs != 1 && a₂.natAbs != 1`
    (← mkLeCnstr p (.combine c₁ c₂)).assert
  else
    assert! a₁.natAbs != 1 && a₂.natAbs != 1
    throwError "NIY"

def resolveDvdConflict (c : DvdCnstr) : GoalM Unit := do
  trace[grind.cutsat.conflict] "{← c.denoteExpr}"
  let d := c.d
  let .add a _ p := c.p | c.throwUnexpected
  (← mkDvdCnstr (a.gcd d) p (.elim c)).assert

def decideVar (x : Var) : GoalM Unit := do
  let lower? ← getBestLower? x
  let upper? ← getBestUpper? x
  let dvd? := (← get').dvdCnstrs[x]!
  match lower?, upper?, dvd? with
  | none, none, none =>
    setAssignment x 0
  | some (lower, _), none, none =>
    setAssignment x lower
  | none, some (upper, _), none =>
    setAssignment x upper
  | some (lower, c₁), some (upper, c₂), none =>
    if lower ≤ upper then
      setAssignment x lower
    else
      trace[grind.cutsat.conflict] "{lower} ≤ {← getVar x} ≤ {upper}"
      resolveLowerUpperConflict c₁ c₂
  | none, none, some cₚ =>
    if let some (_, v) ← getDvdSolutions? cₚ then
      setAssignment x v
    else
      resolveDvdConflict cₚ
  | some (lower, _), none, some cₚ =>
    if let some (d, b) ← getDvdSolutions? cₚ then
      /-
      - `x ≥ lower ∧ x = k*d + b`
      - `k*d + b ≥ lower`
      - `k ≥ cdiv (lower - b) d`
      - So, we take `x = (cdiv (lower - b) d)*d + b`
      -/
      setAssignment x ((Int.Linear.cdiv (lower - b) d)*d + b)
    else
      resolveDvdConflict cₚ
  | none, some (upper, _), some cₚ =>
    if let some (d, b) ← getDvdSolutions? cₚ then
      /-
      - `x ≤ upper ∧ x = k*d +  b`
      - `k*d + b ≤ upper`
      - `k ≤ (upper - b)/d`
      - So, we take `x = ((upper - b)/d)*d + b`
      -/
      setAssignment x (((upper - b)/d)*d + b)
    else
      resolveDvdConflict cₚ
  | _, _, _ =>
    -- TODO: cases containing a divisibility constraint.
    -- TODO: remove the following
    setAssignment x 0

/-- Returns `true` if we already have a complete assignment / model. -/
def hasAssignment : GoalM Bool := do
  return (← get').vars.size == (← get').assignment.size

private def isDone : GoalM Bool := do
  if (← hasAssignment) then
    return true
  if (← isInconsistent) then
    return true
  return false

/-- Search for an assignment/model for the linear constraints. -/
def searchAssigment : GoalM Unit := do
  repeat
    if (← isDone) then
      return ()
    let x : Var := (← get').assignment.size
    decideVar x

end Lean.Meta.Grind.Arith.Cutsat
