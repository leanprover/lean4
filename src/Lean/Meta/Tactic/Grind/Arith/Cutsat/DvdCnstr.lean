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

def DvdCnstr.norm (c : DvdCnstr) : DvdCnstr :=
  let c := if c.p.isSorted then
    c
  else
    { d := c.d, p := c.p.norm, h :=.norm c }
  let g := c.p.gcdCoeffs c.d
  if c.p.getConst % g == 0 && g != 1 then
    { d := c.d/g, p := c.p.div g, h := .divCoeffs c }
  else
    c

/--
Given an equation `c₁` containing the monomial `a*x`, and a divisibility constraint `c₂`
containing the monomial `b*x`, eliminate `x` by applying substitution.
-/
def DvdCnstr.applyEq (a : Int) (x : Var) (c₁ : EqCnstr) (b : Int) (c₂ : DvdCnstr) : GoalM DvdCnstr := do
  let p := c₁.p
  let q := c₂.p
  let d := Int.ofNat (a * c₂.d).natAbs
  let p := (q.mul a |>.combine (p.mul (-b)))
  trace[grind.cutsat.subst] "{← getVar x}, {← c₁.pp}, {← c₂.pp}"
  return { d, p, h := .subst x c₁ c₂ }

partial def DvdCnstr.applySubsts (c : DvdCnstr) : GoalM DvdCnstr := withIncRecDepth do
  let some (b, x, c₁) ← c.p.findVarToSubst | return c
  let a := c₁.p.coeff x
  let c ← c.applyEq a x c₁ b
  applySubsts c

/-- Asserts divisibility constraint. -/
partial def DvdCnstr.assert (c : DvdCnstr) : GoalM Unit := withIncRecDepth do
  if (← inconsistent) then return ()
  trace[grind.cutsat.dvd] "{← c.pp}"
  let c ← c.norm.applySubsts
  if c.isUnsat then
    trace[grind.cutsat.dvd.unsat] "{← c.pp}"
    setInconsistent (.dvd c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.dvd.trivial] "{← c.pp}"
    return ()
  let d₁ := c.d
  let .add a₁ x p₁ := c.p | c.throwUnexpected
  if (← c.satisfied) == .false then
    resetAssignmentFrom x
  if let some c' := (← get').dvds[x]! then
    trace[grind.cutsat.dvd.solve] "{← c.pp}, {← c'.pp}"
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
    let combine := { d := d₁*d₂, p := .add d x (α_d₂_p₁.combine β_d₁_p₂), h := .solveCombine c c' : DvdCnstr }
    trace[grind.cutsat.dvd.solve.combine] "{← combine.pp}"
    modify' fun s => { s with dvds := s.dvds.set x none}
    combine.assert
    let a₂_p₁ := p₁.mul a₂
    let a₁_p₂ := p₂.mul (-a₁)
    let elim := { d, p := a₂_p₁.combine a₁_p₂, h := .solveElim c c' : DvdCnstr }
    trace[grind.cutsat.dvd.solve.elim] "{← elim.pp}"
    elim.assert
  else
    trace[grind.cutsat.dvd.update] "{← c.pp}"
    c.p.updateOccs
    modify' fun s => { s with dvds := s.dvds.set x (some c) }

builtin_grind_propagator propagateDvd ↓Dvd.dvd := fun e => do
  let_expr Dvd.dvd _ inst a b ← e | return ()
  unless (← isInstDvdInt inst) do return ()
  let some d ← getIntValue? a
    | reportIssue! "non-linear divisibility constraint found{indentExpr e}"
      return ()
  if (← isEqTrue e) then
    let p ← toPoly b
    let c := { d, p, h := .expr (← mkOfEqTrue (← mkEqTrueProof e)) : DvdCnstr }
    trace[grind.cutsat.assert.dvd] "{← c.pp}"
    c.assert
  else if (← isEqFalse e) then
    /-
    TODO: we have `¬ a ∣ b`, we should assert
    `∃ x z, b = a*x + z ∧ 1 ≤ z < a`
    -/
    return ()

end Lean.Meta.Grind.Arith.Cutsat
