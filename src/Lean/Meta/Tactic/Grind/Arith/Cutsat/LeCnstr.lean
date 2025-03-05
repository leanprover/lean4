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

def LeCnstr.norm (c : LeCnstr) : LeCnstr :=
  let c := if c.p.isSorted then
    c
  else
    { p := c.p.norm, h := .norm c }
  let k := c.p.gcdCoeffs'
  if k != 1 then
    { p := c.p.div k, h := .divCoeffs c }
  else
    c

/--
Given an equation `c₁` containing the monomial `a*x`, and an inequality constraint `c₂`
containing the monomial `b*x`, eliminate `x` by applying substitution.
-/
def LeCnstr.applyEq (a : Int) (x : Var) (c₁ : EqCnstr) (b : Int) (c₂ : LeCnstr) : GoalM LeCnstr := do
  let p := c₁.p
  let q := c₂.p
  let p := if a ≥ 0 then
    q.mul a |>.combine (p.mul (-b))
  else
    p.mul b |>.combine (q.mul (-a))
  trace[grind.cutsat.subst] "{← getVar x}, {← c₁.pp}, {← c₂.pp}"
  return { p, h := .subst x c₁ c₂ }

partial def LeCnstr.applySubsts (c : LeCnstr) : GoalM LeCnstr := withIncRecDepth do
  let some (b, x, c₁) ← c.p.findVarToSubst | return c
  let a := c₁.p.coeff x
  let c ← c.applyEq a x c₁ b
  applySubsts c

def _root_.Int.Linear.Poly.isNegEq (p₁ p₂ : Poly) : Bool :=
  match p₁, p₂ with
  | .num k₁, .num k₂ => k₁ == -k₂
  | .add a₁ x p₁, .add a₂ y p₂ => a₁ == -a₂ && x == y && isNegEq p₁ p₂
  | _, _ => false

def LeCnstr.erase (c : LeCnstr) : GoalM Unit := do
  let .add a x _ := c.p | c.throwUnexpected
  if a < 0 then
    modify' fun s => { s with lowers := s.lowers.modify x fun cs' => cs'.filter fun c' => c'.p != c.p }
  else
    modify' fun s => { s with uppers := s.uppers.modify x fun cs' => cs'.filter fun c' => c'.p != c.p }

/--
Given a lower (upper) bound constraint `c`, tries to find
an imply equality by searching a upper (lower) bound constraint `c'` such that
`c.p == -c'.p`
-/
private def findEq (c : LeCnstr) : GoalM Bool := do
  let .add a x _ := c.p | c.throwUnexpected
  let s ← get'
  let cs' := if a < 0 then s.uppers[x]! else s.lowers[x]!
  for c' in cs' do
    if c.p.isNegEq c'.p then
      c'.erase
      let eq := { p := c.p, h := .ofLeGe c c' : EqCnstr }
      trace[grind.debug.cutsat.eq] "new eq: {← eq.pp}"
      eq.assert
      return true
  return false

/--
Applies `p ≤ 0 → p ≠ 0 → p + 1 ≤ 0`
-/
private def refineWithDiseq (c : LeCnstr) : GoalM LeCnstr := do
  let .add _ x _ := c.p | c.throwUnexpected
  let mut c := c
  repeat
    let some c' ← refineWithDiseqStep? x c | return c
    c := c'
  return c
where
  refineWithDiseqStep? (x : Var) (c : LeCnstr) : GoalM (Option LeCnstr) := do
    let s ← get'
    let cs' := s.diseqs[x]!
    for c' in cs' do
      if c.p == c'.p || c.p.isNegEq c'.p then
        -- Remove `c'`
        modify' fun s => { s with diseqs := s.diseqs.modify x fun cs' => cs'.filter fun c => c.p != c'.p }
        return some { p := c.p.addConst 1, h := .ofLeDiseq c c' }
    return none

def LeCnstr.assert (c : LeCnstr) : GoalM Unit := do
  if (← inconsistent) then return ()
  let c ← c.norm.applySubsts
  if c.isUnsat then
    trace[grind.cutsat.le.unsat] "{← c.pp}"
    setInconsistent (.le c)
    return ()
  if c.isTrivial then
    trace[grind.cutsat.le.trivial] "{← c.pp}"
    return ()
  let .add a x _ := c.p | c.throwUnexpected
  if (← findEq c) then
    return ()
  let c ← refineWithDiseq c
  if a < 0 then
    trace[grind.cutsat.le.lower] "{← c.pp}"
    c.p.updateOccs
    modify' fun s => { s with lowers := s.lowers.modify x (·.push c) }
  else
    trace[grind.cutsat.le.upper] "{← c.pp}"
    c.p.updateOccs
    modify' fun s => { s with uppers := s.uppers.modify x (·.push c) }
  if (← c.satisfied) == .false then
    resetAssignmentFrom x

private def reportNonNormalized (e : Expr) : GoalM Unit := do
  reportIssue! "unexpected non normalized inequality constraint found{indentExpr e}"

private def toPolyLe? (e : Expr) : GoalM (Option Poly) := do
  let_expr LE.le _ inst a b ← e | return none
  unless (← isInstLEInt inst) do return none
  let some k ← getIntValue? b
    | reportNonNormalized e; return none
  unless k == 0 do
    reportNonNormalized e; return none
  return some (← toPoly a)

/--
Given an expression `e` that is in `True` (or `False` equivalence class), if `e` is an
integer inequality, asserts it to the cutsat state.
-/
def propagateIfIntLe (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  let some p ← toPolyLe? e | return ()
  let c ← if eqTrue then
    pure { p, h := .expr (← mkOfEqTrue (← mkEqTrueProof e)) : LeCnstr }
  else
    pure { p := p.mul (-1) |>.addConst 1, h := .notExpr p (← mkOfEqFalse (← mkEqFalseProof e)) : LeCnstr }
  trace[grind.cutsat.assert.le] "{← c.pp}"
  c.assert

end Lean.Meta.Grind.Arith.Cutsat
