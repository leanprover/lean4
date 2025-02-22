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
def mkLeCnstr (p : Poly) (h : LeCnstrProof) : GoalM LeCnstr := do
  return { p, h, id := (← mkCnstrId) }

def LeCnstr.norm (c : LeCnstr) : GoalM LeCnstr := do
  let c ← if c.p.isSorted then
    pure c
  else
    mkLeCnstr c.p.norm (.norm c)
  let k := c.p.gcdCoeffs'
  if k != 1 then
    mkLeCnstr (c.p.div k) (.divCoeffs c)
  else
    return c

def assertRelCnstr (c : LeCnstr) : GoalM Unit := do
  if (← isInconsistent) then return ()
  let c ← c.norm
  if c.isUnsat then
    trace[grind.cutsat.le.unsat] "{← c.denoteExpr}"
    let hf ← withProofContext do
      return mkApp4 (mkConst ``Int.Linear.le_unsat) (← getContext) (toExpr c.p) reflBoolTrue (← c.toExprProof)
    closeGoal hf
  else if c.isTrivial then
    trace[grind.cutsat.le.trivial] "{← c.denoteExpr}"
  else
    let .add a x _ := c.p | c.throwUnexpected
    if a < 0 then
      trace[grind.cutsat.le.lower] "{← c.denoteExpr}"
      modify' fun s => { s with lowers := s.lowers.modify x (·.push c) }
    else
      trace[grind.cutsat.le.upper] "{← c.denoteExpr}"
      modify' fun s => { s with uppers := s.uppers.modify x (·.push c) }
    if (← c.satisfied) == .false then
      resetAssignmentFrom x

private def reportNonNormalized (e : Expr) : GoalM Unit := do
  reportIssue! "unexpected non normalized inequality constraint found{indentExpr e}"

private def toPoly? (e : Expr) : GoalM (Option Poly) := do
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
  let some p ← toPoly? e | return ()
  let c ← if eqTrue then
    mkLeCnstr p (.expr (← mkOfEqTrue (← mkEqTrueProof e)))
  else
    mkLeCnstr (p.mul (-1) |>.addConst 1) (.notExpr p (← mkOfEqFalse (← mkEqFalseProof e)))
  trace[grind.cutsat.assert.le] "{← c.denoteExpr}"
  assertRelCnstr c

end Lean.Meta.Grind.Arith.Cutsat
