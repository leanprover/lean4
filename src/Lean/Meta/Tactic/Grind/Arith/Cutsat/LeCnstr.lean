/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt
import Init.Data.Int.OfNat
import Lean.Meta.Tactic.Simp.Arith.Int
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
public section
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
  trace[grind.lia.subst] "{← getVar x}, {← c₁.pp}, {← c₂.pp}"
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
      trace[grind.debug.lia.eq] "new eq: {← eq.pp}"
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

@[export lean_grind_cutsat_assert_le]
def LeCnstr.assertImpl (c : LeCnstr) : GoalM Unit := do
  if (← inconsistent) then return ()
  trace[grind.lia.assert] "{← c.pp}"
  let c ← c.norm.applySubsts
  if c.isUnsat then
    trace[grind.lia.assert.unsat] "{← c.pp}"
    setInconsistent (.le c)
    return ()
  if c.isTrivial then
    trace[grind.lia.assert.trivial] "{← c.pp}"
    return ()
  let .add a x _ := c.p | c.throwUnexpected
  if (← findEq c) then
    return ()
  let c ← refineWithDiseq c
  trace[grind.lia.assert.store] "{← c.pp}"
  c.p.updateOccs
  if a < 0 then
    modify' fun s => { s with lowers := s.lowers.modify x (·.push c) }
  else
    modify' fun s => { s with uppers := s.uppers.modify x (·.push c) }
  if (← c.satisfied) == .false then
    resetAssignmentFrom x

private def reportNonNormalized (e : Expr) : GoalM Unit := do
  reportIssue! "unexpected non normalized inequality constraint found{indentExpr e}"

private def toPolyLe? (e : Expr) : GoalM (Option Poly) := do
  let_expr LE.le _ inst a b ← e | return none
  unless (← Structural.isInstLEInt inst) do return none
  let some k ← getIntValue? b
    | reportNonNormalized e; return none
  unless k == 0 do
    reportNonNormalized e; return none
  return some (← toPoly a)

/-- Asserts a constraint coming from the core. -/
private def LeCnstr.assertCore (c : LeCnstr) : GoalM Unit := do
  if let some (re, rp, p) ← c.p.normCommRing? then
    let c := { p, h := .commRingNorm c re rp : LeCnstr}
    c.assert
  else
    c.assert

/--
Given an expression `e` that is in `True` (or `False` equivalence class), if `e` is an
integer inequality, asserts it to the cutsat state.
-/
def propagateIntLe (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  let some p ← toPolyLe? e | return ()
  let c ← if eqTrue then
    pure { p, h := .core e : LeCnstr }
  else
    pure { p := p.mul (-1) |>.addConst 1, h := .coreNeg e p : LeCnstr }
  c.assertCore

def propagateNatLe (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  let_expr LE.le _ _ a b := e | return ()
  let thm := if eqTrue then mkConst ``Nat.ToInt.of_le else mkConst ``Nat.ToInt.of_not_le
  let gen ← getGeneration e
  let (a', h₁) ← natToInt a
  let (b', h₂) ← natToInt b
  let thm := mkApp6 thm a b a' b' h₁ h₂
  let (a', b') := if eqTrue then (a', b') else (mkIntAdd b' (mkIntLit 1), a')
  let lhs ← toLinearExpr a' gen
  let rhs ← toLinearExpr b' gen
  let p := lhs.sub rhs |>.norm
  let c := { p, h := .coreToInt e eqTrue thm lhs rhs : LeCnstr }
  c.assertCore

def propagateToIntLe (e : Expr) (eqTrue : Bool) : ToIntM Unit := do
  let some thm ← if eqTrue then getOfLE? else getOfNotLE? | return ()
  let_expr LE.le _ _ a b := e | return ()
  let gen ← getGeneration e
  let (a', h₁) ← toInt a
  let (b', h₂) ← toInt b
  let thm := mkApp6 thm a b a' b' h₁ h₂
  let (a', b') := if eqTrue then (a', b') else (mkIntAdd b' (mkIntLit 1), a')
  let lhs ← toLinearExpr a' gen
  let rhs ← toLinearExpr b' gen
  let p := lhs.sub rhs |>.norm
  let c := { p, h := .coreToInt e eqTrue thm lhs rhs : LeCnstr }
  c.assertCore

def propagateLe (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  unless (← getConfig).lia do return ()
  let_expr LE.le α _ _ _ := e | return ()
  if α.isConstOf ``Nat then
    propagateNatLe e eqTrue
  else if α.isConstOf ``Int then
    propagateIntLe e eqTrue
  else ToIntM.run α do
    propagateToIntLe e eqTrue

def propagateLt (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  unless (← getConfig).lia do return ()
  let_expr LT.lt α _ a b := e | return ()
  ToIntM.run α do
    let some thm ← if eqTrue then getOfLT? else getOfNotLT? | return ()
    let gen ← getGeneration e
    let (a', h₁) ← toInt a
    let (b', h₂) ← toInt b
    let thm := mkApp6 thm a b a' b' h₁ h₂
    let (a', b') := if eqTrue then (mkIntAdd a' (mkIntLit 1), b') else (b', a')
    let lhs ← toLinearExpr a' gen
    let rhs ← toLinearExpr b' gen
    let p := lhs.sub rhs |>.norm
    let c := { p, h := .coreToInt e eqTrue thm lhs rhs : LeCnstr }
    c.assert

end Lean.Meta.Grind.Arith.Cutsat
