/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.ProveEq
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
public section
namespace Lean.Meta.Grind.Arith.Cutsat
/-!
CommRing interface for cutsat. We use it to normalize nonlinear polynomials.
-/

/-- Returns `true` if `p` contains a nonlinear monomial. -/
def _root_.Int.Linear.Poly.isNonlinear (p : Poly) : GoalM Bool := do
  let .add _ x p := p | return false
  if (← getVar x).isAppOf ``HMul.hMul || (← getVar x).isAppOf ``HPow.hPow then return true
  p.isNonlinear

def _root_.Int.Linear.Poly.getGeneration (p : Poly) : GoalM Nat := do
  go p 0
where
  go : Poly → Nat → GoalM Nat
  | .num _, gen => return gen
  | .add _ x p, gen => do go p (max (← Grind.getGeneration (← getVar x)) gen)

def getIntRingId? : GoalM (Option Nat) := do
  CommRing.getCommRingId? (← getIntExpr)

/-- Normalize the polynomial using `CommRing`-/
def _root_.Int.Linear.Poly.normCommRing? (p : Poly) : GoalM (Option (CommRing.RingExpr × CommRing.Poly × Poly)) := do
  unless (← p.isNonlinear) do return none
  let some ringId ← getIntRingId? | return none
  CommRing.RingM.run ringId do
    let e ← p.denoteExpr'
    -- TODO: we can avoid the following statement if we construct the `Int` denotation using
    -- Internalized operators instead of `mkIntMul` and `mkIntAdd`
    let e ← shareCommon (← canon e)
    let gen ← p.getGeneration
    let some re ← CommRing.reify? e (gen := gen) | return none
    let some p' ← re.toPolyM? | return none
    let e' ← p'.denoteExpr
    let e' ← preprocessLight e'
    /-
    **Note**: We are reusing the `IntModule` virtual parent.
    **TODO**: Investigate whether we should have a custom virtual parent for cutsat
    -/
    internalize e' gen (some getIntModuleVirtualParent)
    let p'' ← toPoly e'
    if p == p'' then return none
    modify' fun s => { s with usedCommRing := true }
    trace[grind.lia.assert.nonlinear] "{← p.pp} ===> {← p''.pp}"
    return some (re, p', p'')

end Lean.Meta.Grind.Arith.Cutsat
