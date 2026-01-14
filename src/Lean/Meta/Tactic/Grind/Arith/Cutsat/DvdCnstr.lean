/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Init.Data.Int.OfNat
import Init.Grind.Propagator
import Lean.Meta.Tactic.Grind.Simp
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
import Lean.Meta.NatInstTesters
public section
namespace Lean.Meta.Grind.Arith.Cutsat

def DvdCnstr.norm (c : DvdCnstr) : DvdCnstr :=
  let c := if c.p.isSorted then
    c
  else
    { d := c.d, p := c.p.norm, h :=.norm c }
  let g := c.p.gcdCoeffs c.d
  let g := if c.d < 0 then -g else g
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
  trace[grind.debug.lia.subst] "{← getVar x}, {← c₁.pp}, {← c₂.pp}"
  return { d, p, h := .subst x c₁ c₂ }

partial def DvdCnstr.applySubsts (c : DvdCnstr) : GoalM DvdCnstr := withIncRecDepth do
  let some (b, x, c₁) ← c.p.findVarToSubst | return c
  let a := c₁.p.coeff x
  let c ← c.applyEq a x c₁ b
  applySubsts c

/-- Asserts divisibility constraint. -/
partial def DvdCnstr.assert (c : DvdCnstr) : GoalM Unit := withIncRecDepth do
  if (← inconsistent) then return ()
  trace[grind.lia.assert] "{← c.pp}"
  let c ← c.norm.applySubsts
  if c.isUnsat then
    trace[grind.lia.assert.unsat] "{← c.pp}"
    setInconsistent (.dvd c)
    return ()
  if c.isTrivial then
    trace[grind.lia.assert.trivial] "{← c.pp}"
    return ()
  let d₁ := c.d
  let .add a₁ x p₁ := c.p | c.throwUnexpected
  if (← c.satisfied) == .false then
    resetAssignmentFrom x
  if let some c' := (← get').dvds[x]! then
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
    modify' fun s => { s with dvds := s.dvds.set x none}
    combine.assert
    let a₂_p₁ := p₁.mul a₂
    let a₁_p₂ := p₂.mul (-a₁)
    let elim := { d, p := a₂_p₁.combine a₁_p₂, h := .solveElim c c' : DvdCnstr }
    elim.assert
  else
    trace[grind.lia.assert.store] "{← c.pp}"
    c.p.updateOccs
    modify' fun s => { s with dvds := s.dvds.set x (some c) }

/-- Asserts a constraint coming from the core. -/
private def DvdCnstr.assertCore (c : DvdCnstr) : GoalM Unit := do
  if let some (re, rp, p) ← c.p.normCommRing? then
    let c := { c with p, h := .commRingNorm c re rp : DvdCnstr}
    c.assert
  else
    c.assert

def propagateIntDvd (e : Expr) : GoalM Unit := do
  let_expr Dvd.dvd _ inst a b ← e | return ()
  unless (← Structural.isInstDvdInt inst) do return ()
  let some d ← getIntValue? a
    | reportIssue! "non-linear divisibility constraint found{indentExpr e}"; return ()
  if (← isEqTrue e) then
    let p ← toPoly b
    let c := { d, p, h := .core e : DvdCnstr }
    c.assertCore
  else if (← isEqFalse e) then
    pushNewFact <| mkApp4 (mkConst ``Int.Linear.of_not_dvd) a b eagerReflBoolTrue (mkOfEqFalseCore e (← mkEqFalseProof e))

def propagateNatDvd (e : Expr) : GoalM Unit := do
  let_expr Dvd.dvd _ inst d₀ a := e | return ()
  unless (← Structural.isInstDvdNat inst) do return ()
  let some d ← getNatValue? d₀
    | reportIssue! "non-linear divisibility constraint found{indentExpr e}"; return ()
  if (← isEqTrue e) then
    let (d', h₁) ← natToInt d₀
    let (a', h₂) ← natToInt a
    let gen ← getGeneration e
    let e' ← toLinearExpr a' gen
    let p := e'.norm
    let thm := mkApp6 (mkConst ``Nat.ToInt.of_dvd) d₀ a d' a' h₁ h₂
    let c := { d, p, h := .coreOfNat e thm d e' : DvdCnstr }
    c.assertCore
  else if (← isEqFalse e) then
    pushNewFact <| mkApp3 (mkConst ``Nat.emod_pos_of_not_dvd) d₀ a (mkOfEqFalseCore e (← mkEqFalseProof e))

builtin_grind_propagator propagateDvd ↓Dvd.dvd := fun e => do
  unless (← getConfig).lia do return ()
  let_expr Dvd.dvd α _ _ _ ← e | return ()
  if α.isConstOf ``Nat then
    propagateNatDvd e
  else
    propagateIntDvd e

end Lean.Meta.Grind.Arith.Cutsat
