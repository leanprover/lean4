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

def mkEqCnstr (p : Poly) (h : EqCnstrProof) : RingM EqCnstr := do
  let id := (← getRing).nextId
  let sugar := p.degree
  modifyRing fun s => { s with nextId := s.nextId + 1 }
  return { sugar, p, h, id }

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

/-- Simplifies `c₁` using `c₂`. -/
def EqCnstr.simplify1 (c₁ c₂ : EqCnstr) : RingM (Option EqCnstr) := do
  let some r := c₁.p.simp? c₂.p (← nonzeroChar?) | return none
  let c := { c₁ with
    p := r.p
    h := .simp r.k₁ c₁ r.k₂ r.m₂ c₂
  }
  trace_goal[grind.ring.simp] "{← c.p.denoteExpr}"
  return some c

/-- Keep simplifying `c` with `c'` until it is not applicable anymore. -/
def EqCnstr.simplifyWith (c c' : EqCnstr) : RingM EqCnstr := do
  let mut c := c
  repeat
    checkSystem "ring"
    let some r ← c.simplify1 c' | return c
    trace_goal[grind.debug.ring.simp] "simplifying{indentD (← c.denoteExpr)}\nwith{indentD (← c'.denoteExpr)}"
    c := r
  return c

/-- Simplify the given equation constraint using the current basis. -/
def EqCnstr.simplify (c : EqCnstr) : RingM EqCnstr := do
  let mut c := c
  repeat
    let some c' ← c.p.findSimp? |
      trace_goal[grind.debug.ring.simp] "simplified{indentD (← c.denoteExpr)}"
      return c
    c ← c.simplifyWith c'
  return c

/-- Returns `true` if `c.p` is the constant polynomial. -/
def EqCnstr.checkConstant (c : EqCnstr) : RingM Bool := do
  let .num k := c.p | return false
  if k == 0 then
    trace_goal[grind.ring.assert.trivial] "{← c.denoteExpr}"
  else if (← hasChar) then
    setUnsatEq c
  else
    -- Remark: we currently don't do anything if the characteristic is not known.
    trace_goal[grind.ring.assert.discard] "{← c.denoteExpr}"
  return true

/--
Simplifies and checks whether the resulting constraint is trivial (i.e., `0 = 0`),
or inconsistent (i.e., `k = 0` where `k % c != 0` for a comm-ring with characteristic `c`),
and returns `none`. Otherwise, returns the simplified constraint.
-/
def EqCnstr.simplifyAndCheck (c : EqCnstr) : RingM (Option EqCnstr) := do
  let c ← c.simplify
  if (← c.checkConstant) then
    return none
  else
    return some c

def EqCnstr.simplifyBasis (c : EqCnstr) : RingM Unit := do
  let .add _ m _ := c.p | return ()
  let .mult pw _ := m | return ()
  let x := pw.x
  let cs := (← getRing).varToBasis[x]!
  let cs ← cs.filterMapM fun c' => do
    let .add _ m' _ := c'.p | return none
    if m.divides m' then
      let c' ← c'.simplifyWith c'
      if (← c'.checkConstant) then
        return none
      else
        return some c'
    else
      return some c'
  modifyRing fun s => { s with varToBasis := s.varToBasis.set x cs }

def EqCnstr.addToQueue (c : EqCnstr) : RingM Unit := do
  trace_goal[grind.ring.assert.queue] "{← c.denoteExpr}"
  modifyRing fun s => { s with queue := s.queue.insert c }

def EqCnstr.superposeWith (c : EqCnstr) : RingM Unit := do
  trace[grind.ring.superpose] "{← c.denoteExpr}"
  return ()

/--
Tries to convert the leading monomial into a monic one.

It exploits the fact that given a polynomial with leading coefficient `k`,
if the ring has a nonzero characteristic `p` and `gcd k p = 1`, then
`k` has an inverse.

It also handles the easy case where `k` is `-1`.
-/
def EqCnstr.toMonic (c : EqCnstr) : RingM EqCnstr := do
  let k := c.p.lc
  if k == 1 then return c
  if let some p ← nonzeroChar? then
    let (g, α, _β) := gcdExt k p
    if g == 1 then
      -- `α*k + β*p = 1`
      -- `α*k = 1 (mod p)`
      let α := if α < 0 then α % p else α
      return { c with p := c.p.mulConstC α p, h := .mul α c }
    else
      return c
  else if k == -1 then
    return { c with p := c.p.mulConst (-1), h := .mul (-1) c }
  else
    return c

def EqCnstr.addToBasisAfterSimp (c : EqCnstr) : RingM Unit := do
  let c ← c.toMonic
  c.simplifyBasis
  c.superposeWith
  let .add _ m _ := c.p | return ()
  let .mult pw _ := m | return ()
  trace_goal[grind.ring.assert.basis] "{← c.denoteExpr}"
  modifyRing fun s => { s with varToBasis := s.varToBasis.modify pw.x (c :: ·) }

def EqCnstr.addToBasis (c : EqCnstr) : RingM Unit := do
  let some c ← c.simplifyAndCheck | return ()
  c.addToBasisAfterSimp

def addNewEq (c : EqCnstr) : RingM Unit := do
  let some c ← c.simplifyAndCheck | return ()
  if c.p.degree == 1 then
    c.addToBasisAfterSimp
  else
    c.addToQueue

@[export lean_process_ring_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  let some ringId ← inSameRing? a b | return ()
  RingM.run ringId do
    trace_goal[grind.ring.assert] "{← mkEq a b}"
    let some ra ← toRingExpr? a | return ()
    let some rb ← toRingExpr? b | return ()
    let p ← (ra.sub rb).toPolyM
    -- TODO: delete this `if` after simplifier is fully integrated
    if let .num k := p then
      if k == 0 then
        trace_goal[grind.ring.assert.trivial] "{← p.denoteExpr} = 0"
      else if (← hasChar) then
        trace_goal[grind.ring.assert.unsat] "{← p.denoteExpr} = 0"
        setEqUnsat k a b ra rb
      else
        -- Remark: we currently don't do anything if the characteristic is not known.
        trace_goal[grind.ring.assert.discard] "{← p.denoteExpr} = 0"
      return ()
    addNewEq (← mkEqCnstr p (.core a b ra rb))

@[export lean_process_ring_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  let some ringId ← inSameRing? a b | return ()
  RingM.run ringId do
    trace_goal[grind.ring.assert] "{mkNot (← mkEq a b)}"
    let some ra ← toRingExpr? a | return ()
    let some rb ← toRingExpr? b | return ()
    let p ← (ra.sub rb).toPolyM
    if let .num k := p then
      if k == 0 then
        trace_goal[grind.ring.assert.unsat] "{← p.denoteExpr} ≠ 0"
        setNeUnsat a b ra rb
      else
        -- Remark: if the characteristic is known, it is trivial.
        -- Otherwise, we don't do anything.
        trace_goal[grind.ring.assert.trivial] "{← p.denoteExpr} ≠ 0"
      return ()
    trace_goal[grind.ring.assert.store] "{← p.denoteExpr} ≠ 0"
    -- TODO: save disequalitys

end Lean.Meta.Grind.Arith.CommRing
