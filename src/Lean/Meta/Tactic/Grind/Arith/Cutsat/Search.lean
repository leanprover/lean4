/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.RelCnstr

namespace Lean.Meta.Grind.Arith.Cutsat

private def throwUnexpectedCnstr (cₚ : RelCnstrWithProof) : GoalM α := do
  throwError "`grind` internal error, unexpected{indentExpr (← cₚ.denoteExpr)} "

def getBestLower? (x : Var) : GoalM (Option (Int × RelCnstrWithProof)) := do
  let s ← get'
  let mut best? := none
  for cₚ in s.lowers[x]! do
    let .add k _ p := cₚ.c.p
      | throwUnexpectedCnstr cₚ
    let some v ← p.eval?
      | pure ()
    let lower' := Int.Linear.cdiv v (-k)
    if let some (lower, _) := best? then
      if lower' > lower then
        best? := some (lower', cₚ)
    else
      best? := some (lower', cₚ)
  return best?

def getBestUpper? (x : Var) : GoalM (Option (Int × RelCnstrWithProof)) := do
  let s ← get'
  let mut best? := none
  for cₚ in s.uppers[x]! do
    let .add k _ p := cₚ.c.p
      | throwUnexpectedCnstr cₚ
    let some v ← p.eval?
      | pure ()
    let upper' := (-v) / k
    if let some (upper, _) := best? then
      if upper' < upper then
        best? := some (upper', cₚ)
    else
      best? := some (upper', cₚ)
  return best?

private partial def setAssignment (x : Var) (v : Int) : GoalM Unit := do
  if x == (← get').assignment.size then
    trace[grind.cutsat.assign] "{(← getVar x)} := {v}"
    modify' fun s => { s with assignment := s.assignment.push v }
  else if x > (← get').assignment.size then
    modify' fun s => { s with assignment := s.assignment.push 0 }
    setAssignment x v
  else
    throwError "`grind` internal error, variable is already assigned"

def resolveLowerUpperConflict (c₁ c₂ : RelCnstrWithProof) : GoalM Unit := do
  -- TODO
  trace[grind.cutsat.conflict] "{← c₁.denoteExpr}, {← c₂.denoteExpr}"
  return ()

def decideVar (x : Var) : GoalM Unit := do
  let lower? ← getBestLower? x
  let upper? ← getBestUpper? x
  let div? := (← get').dvdCnstrs[x]!
  match lower?, upper?, div? with
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
      -- TODO: remove the following
      setAssignment x 0
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
