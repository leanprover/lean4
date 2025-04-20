/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof

namespace Lean.Meta.Grind.Arith.CommRing

private def toRingExpr? (ringId : Nat) (e : Expr) : GoalM (Option RingExpr) := do
  let ring ← getRing ringId
  if let some re := ring.denote.find? { expr := e } then
    return some re
  else if let some x := ring.varMap.find? { expr := e } then
    return some (.var x)
  else
    reportIssue! "failed to convert to ring expression{indentExpr e}"
    return none

/-- Returns `some ringId` if `a` and `b` are elements of the same ring. -/
private def inSameRing? (a b : Expr) : GoalM (Option Nat) := do
  let some ringId ← getTermRingId? a | return none
  let some ringId' ← getTermRingId? b | return none
  unless ringId == ringId' do return none -- This can happen when we have heterogeneous equalities
  return ringId

@[export lean_process_ring_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  let some ringId ← inSameRing? a b | return ()
  trace[grind.ring] "{← mkEq a b}"
  let some ra ← toRingExpr? ringId a | return ()
  let some rb ← toRingExpr? ringId b | return ()
  let p ← toPoly ringId (ra.sub rb)
  if let .num k := p then
    if k != 0 && (← hasChar ringId) then
      setEqUnsat ringId k a b ra rb
      return ()
  -- TODO: save equality

@[export lean_process_ring_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  let some ringId ← inSameRing? a b | return ()
  trace[grind.ring] "{mkNot (← mkEq a b)}"
  let some ra ← toRingExpr? ringId a | return ()
  let some rb ← toRingExpr? ringId b | return ()
  let p ← toPoly ringId (ra.sub rb)
  if p == .num 0 then
    setNeUnsat ringId a b ra rb
    return ()
  -- TODO: save disequalitys

end Lean.Meta.Grind.Arith.CommRing
