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
Remark: if the current ring does not satisfy the property
```
∀ (k : Nat) (a : α), k ≠ 0 → OfNat.ofNat (α := α) k * a = 0 → a = 0
```
then the leading coefficient of the equation must also divide `k`
-/
def _root_.Lean.Grind.CommRing.Mon.findSimp? (k : Int) (m : Mon) : RingM (Option EqCnstr) := do
  let noZeroDiv ← noZeroDivisors
  let rec go : Mon → RingM (Option EqCnstr)
    | .unit => return none
    | .mult pw m' => do
      for c in (← getRing).varToBasis[pw.x]! do
        if noZeroDiv || (c.p.lc ∣ k) then
        if c.p.divides m then
          return some c
      go m'
  go m

/--
Returns `some c`, where `c` is an equation from the basis whose leading monomial divides some
monomial in `p`.
-/
def _root_.Lean.Grind.CommRing.Poly.findSimp? (p : Poly) : RingM (Option EqCnstr) := do
  match p with
  | .num _ => return none
  | .add k m p =>
    match (← m.findSimp? k) with
    | some c => return some c
    | none => p.findSimp?

/-- Simplifies `d.p` using `c`, and returns an extended polynomial derivation. -/
def PolyDerivation.simplify1 (d : PolyDerivation) (c : EqCnstr) : RingM (Option PolyDerivation) := do
  let some r := d.p.simp? c.p (← nonzeroChar?) | return none
  trace_goal[grind.ring.simp] "{← r.p.denoteExpr}"
  return some <| .step r.p r.k₁ d r.k₂ r.m₂ c

/-- Simplifies `d.p` using `c` until it is not applicable anymore, and returns an extended polynomial derivation.  -/
def PolyDerivation.simplifyWith (d : PolyDerivation) (c : EqCnstr) : RingM PolyDerivation := do
  let mut d := d
  repeat
    checkSystem "ring"
    let some r ← d.simplify1 c | return d
    trace_goal[grind.debug.ring.simp] "simplifying{indentD (← d.denoteExpr)}\nwith{indentD (← c.denoteExpr)}"
    d := r
  return d

/-- Simplified `d.p` using the current basis, and returns the extended polynomial derivation. -/
def PolyDerivation.simplify (d : PolyDerivation) : RingM PolyDerivation := do
  let mut d := d
  repeat
    let some c ← d.p.findSimp? |
      trace_goal[grind.debug.ring.simp] "simplified{indentD (← d.denoteExpr)}"
      return d
    d ← d.simplifyWith c
  return d

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
    c.setUnsat
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

/-- Returns `true` if `c.d.p` is the constant polynomial. -/
def DiseqCnstr.checkConstant (c : DiseqCnstr) : RingM Bool := do
  let .num k := c.d.p | return false
  if k == 0 then
    c.setUnsat
  else
    trace_goal[grind.ring.assert.trivial] "{← c.denoteExpr}"
  return true

def DiseqCnstr.simplify (c : DiseqCnstr) : RingM DiseqCnstr := do
  return { c with d := (← c.d.simplify) }

def saveDiseq (c : DiseqCnstr) : RingM Unit := do
  trace_goal[grind.ring.assert.store] "{← c.denoteExpr}"
  modifyRing fun s => { s with diseqs := s.diseqs.push c }

def addNewDiseq (c : DiseqCnstr) : RingM Unit := do
  let c ← c.simplify
  if (← c.checkConstant) then
    return ()
  saveDiseq c

@[export lean_process_ring_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  let some ringId ← inSameRing? a b | return ()
  RingM.run ringId do
    trace_goal[grind.ring.assert] "{← mkEq a b}"
    let some ra ← toRingExpr? a | return ()
    let some rb ← toRingExpr? b | return ()
    let p ← (ra.sub rb).toPolyM
    addNewEq (← mkEqCnstr p (.core a b ra rb))

@[export lean_process_ring_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  let some ringId ← inSameRing? a b | return ()
  RingM.run ringId do
    trace_goal[grind.ring.assert] "{mkNot (← mkEq a b)}"
    let some ra ← toRingExpr? a | return ()
    let some rb ← toRingExpr? b | return ()
    let p ← (ra.sub rb).toPolyM
    addNewDiseq {
      lhs := a, rhs := b
      rlhs := ra, rrhs := rb
      d := .input p
    }

end Lean.Meta.Grind.Arith.CommRing
