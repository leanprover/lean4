/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof

namespace Lean.Meta.Grind.Arith.CommRing

private def toRingExpr? (e : Expr) (ringId : Nat) : GoalM (Option RingExpr) := do
  let ring ← getRing ringId
  if let some re := ring.denote.find? { expr := e } then
    return some re
  else if let some x := ring.varMap.find? { expr := e } then
    return some (.var x)
  else
    reportIssue! "failed to convert to ring expression{indentExpr e}"
    return none

@[export lean_process_ring_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  trace[grind.ring] "{← mkEq a b}"
  -- TODO

@[export lean_process_ring_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  let some ringId ← getTermRingId? a | return ()
  let some ringId' ← getTermRingId? b | return ()
  unless ringId == ringId' do return () -- This can happen when we have heterogeneous equalities
  trace[grind.ring] "{mkNot (← mkEq a b)}"
  let some e₁ ← toRingExpr? a ringId | return ()
  let some e₂ ← toRingExpr? b ringId | return ()
  let p ← toPoly (e₁.sub e₂) ringId
  if p == .num 0 then
    setNeUnsat ringId a b e₁ e₂
    return ()
  -- TODO: save disequalitys

end Lean.Meta.Grind.Arith.CommRing
