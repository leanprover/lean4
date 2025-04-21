/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr

namespace Lean.Meta.Grind.Arith.CommRing
/-- Returns `some ringId` if `a` and `b` are elements of the same ring. -/
private def inSameRing? (a b : Expr) : GoalM (Option Nat) := do
  let some ringId ← getTermRingId? a | return none
  let some ringId' ← getTermRingId? b | return none
  unless ringId == ringId' do return none -- This can happen when we have heterogeneous equalities
  return ringId

/--
Returns the ring expression denoting the given Lean expression.
Recall that we compute the ring expressions during internalization.
-/
private def toRingExpr? (e : Expr) : RingM (Option RingExpr) := do
  let ring ← getRing
  if let some re := ring.denote.find? { expr := e } then
    return some re
  else if let some x := ring.varMap.find? { expr := e } then
    return some (.var x)
  else
    reportIssue! "failed to convert to ring expression{indentExpr e}"
    return none

/--
Returns `some c`, where `c` is an equation from the basis whose leading monomial divides `m`.
If `unitOnly` is true, only equations with a unit leading coefficient are considered.
-/
def _root_.Lean.Grind.CommRing.Mon.findSimp? (m : Mon) (unitOnly : Bool := false) : RingM (Option EqCnstr) :=
  go m
where
  go : Mon → RingM (Option EqCnstr)
    | .unit => return none
    | .mult pw m' => do
      for c in (← getRing).varToBasis[pw.x]! do
        if !unitOnly || c.p.lc.natAbs == 1 then
        if c.p.divides m then
          return some c
      go m'

/--
Returns `some c`, where `c` is an equation from the basis whose leading monomial divides some
monomial in `p`.
If `unitOnly` is true, only equations with a unit leading coefficient are considered.
-/
def _root_.Lean.Grind.CommRing.Poly.findSimp? (p : Poly) (unitOnly : Bool := false) : RingM (Option EqCnstr) := do
  match p with
  | .num _ => return none
  | .add _ m p =>
    match (← m.findSimp? unitOnly) with
    | some c => return some c
    | none => p.findSimp? unitOnly

/-- Simplify the given equation constraint using the current basis. -/
def simplify (c : EqCnstr) : RingM EqCnstr := do
  let mut c := c
  repeat
    checkSystem "ring"
    let some c' ← c.p.findSimp? | return c
    let some r := c'.p.simp? c.p | unreachable!
    c := { c with
      p := r.p
      h := .simp c' c r.k₁ r.k₂ r.m
    }
    trace[grind.ring.simp] "{← c.p.denoteExpr}"
  return c

@[export lean_process_ring_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  let some ringId ← inSameRing? a b | return ()
  RingM.run ringId do
    trace[grind.ring.assert] "{← mkEq a b}"
    let some ra ← toRingExpr? a | return ()
    let some rb ← toRingExpr? b | return ()
    let p ← (ra.sub rb).toPolyM
    if let .num k := p then
      if k == 0 then
        trace[grind.ring.assert.trivial] "{← p.denoteExpr} = 0"
      else if (← hasChar) then
        trace[grind.ring.assert.unsat] "{← p.denoteExpr} = 0"
        setEqUnsat k a b ra rb
      else
        -- Remark: we currently don't do anything if the characteristic is not known.
        trace[grind.ring.assert.discard] "{← p.denoteExpr} = 0"
      return ()

    trace[grind.ring.assert.store] "{← p.denoteExpr} = 0"
  -- TODO: save equality

@[export lean_process_ring_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  let some ringId ← inSameRing? a b | return ()
  RingM.run ringId do
    trace[grind.ring.assert] "{mkNot (← mkEq a b)}"
    let some ra ← toRingExpr? a | return ()
    let some rb ← toRingExpr? b | return ()
    let p ← (ra.sub rb).toPolyM
    if let .num k := p then
      if k == 0 then
        trace[grind.ring.assert.unsat] "{← p.denoteExpr} ≠ 0"
        setNeUnsat a b ra rb
      else
        -- Remark: if the characteristic is known, it is trivial.
        -- Otherwise, we don't do anything.
        trace[grind.ring.assert.trivial] "{← p.denoteExpr} ≠ 0"
      return ()
    trace[grind.ring.assert.store] "{← p.denoteExpr} ≠ 0"
    -- TODO: save disequalitys

end Lean.Meta.Grind.Arith.CommRing
