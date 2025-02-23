/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Arith.Int
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof

namespace Lean.Meta.Grind.Arith.Cutsat

def mkDvdCnstr (d : Int) (p : Poly) (h : DvdCnstrProof) : GoalM DvdCnstr := do
  return { d, p, h, id := (← mkCnstrId) }

def DvdCnstr.norm (c : DvdCnstr) : GoalM DvdCnstr := do
  let c ← if c.p.isSorted then
    pure c
  else
    mkDvdCnstr c.d c.p.norm (.norm c)
  let g := c.p.gcdCoeffs c.d
  if c.p.getConst % g == 0 && g != 1 then
    mkDvdCnstr (c.d/g) (c.p.div g) (.divCoeffs c)
  else
    return c

/-- Asserts divisibility constraint. -/
partial def DvdCnstr.assert (c : DvdCnstr) : GoalM Unit := withIncRecDepth do
  if (← isInconsistent) then return ()
  let c ← c.norm
  if c.isUnsat then
    trace[grind.cutsat.dvd.unsat] "{← c.denoteExpr}"
    let hf ← withProofContext do
      return mkApp5 (mkConst ``Int.Linear.dvd_unsat) (← getContext) (toExpr c.d) (toExpr c.p) reflBoolTrue (← c.toExprProof)
    closeGoal hf
  else if c.isTrivial then
    trace[grind.cutsat.dvd.trivial] "{← c.denoteExpr}"
    return ()
  else
    let d₁ := c.d
    let .add a₁ x p₁ := c.p | c.throwUnexpected
    if (← c.satisfied) == .false then
      resetAssignmentFrom x
    if let some c' := (← get').dvdCnstrs[x]! then
      trace[grind.cutsat.dvd.solve] "{← c.denoteExpr}, {← c'.denoteExpr}"
      let d₂ := c'.d
      let .add a₂ _ p₂ := c'.p | c'.throwUnexpected
      let (d, α, β) := gcdExt (a₁*d₂) (a₂*d₁)
      /-
      We have that
      `d = α*a₁*d₂ + β*a₂*d₁`
      `d = gcd (a₁*d₂) (a₂*d₁)`
      and two implied divisibility constraints:
      - `d₁*d₂ ∣ d*x + α*d₂*p₁ + β*d₁*p₂`
      - `d ∣ a₂*p₁ - a₁*p₂`
      -/
      let α_d₂_p₁ := p₁.mul (α*d₂)
      let β_d₁_p₂ := p₂.mul (β*d₁)
      let combine ← mkDvdCnstr (d₁*d₂) (.add d x (α_d₂_p₁.combine β_d₁_p₂)) (.solveCombine c c')
      trace[grind.cutsat.dvd.solve.combine] "{← combine.denoteExpr}"
      modify' fun s => { s with dvdCnstrs := s.dvdCnstrs.set x none}
      combine.assert
      let a₂_p₁ := p₁.mul a₂
      let a₁_p₂ := p₂.mul (-a₁)
      let elim ← mkDvdCnstr d (a₂_p₁.combine a₁_p₂) (.solveElim c c')
      trace[grind.cutsat.dvd.solve.elim] "{← elim.denoteExpr}"
      elim.assert
    else
      trace[grind.cutsat.dvd.update] "{← c.denoteExpr}"
      modify' fun s => { s with dvdCnstrs := s.dvdCnstrs.set x (some c) }

builtin_grind_propagator propagateDvd ↓Dvd.dvd := fun e => do
  let_expr Dvd.dvd _ inst a b ← e | return ()
  unless (← isInstDvdInt inst) do return ()
  let some d ← getIntValue? a
    | reportIssue! "non-linear divisibility constraint found{indentExpr e}"
      return ()
  if (← isEqTrue e) then
    let p ← toPoly b
    let c ← mkDvdCnstr d p (.expr (← mkOfEqTrue (← mkEqTrueProof e)))
    trace[grind.cutsat.assert.dvd] "{← c.denoteExpr}"
    c.assert
  else if (← isEqFalse e) then
    /-
    TODO: we have `¬ a ∣ b`, we should assert
    `∃ x z, b = a*x + z ∧ 1 ≤ z < a`
    -/
    return ()

end Lean.Meta.Grind.Arith.Cutsat
