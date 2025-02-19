/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.Arith.Int
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof

namespace Lean.Meta.Grind.Arith.Cutsat
def mkRelCnstrWithProof (c : RelCnstr) (h : RelCnstrProof) : GoalM RelCnstrWithProof := do
  return { c, h, id := (← mkCnstrId) }

abbrev RelCnstrWithProof.isUnsat (cₚ : RelCnstrWithProof) : Bool :=
  cₚ.c.isUnsat

abbrev RelCnstrWithProof.isTrivial (cₚ : RelCnstrWithProof) : Bool :=
  cₚ.c.isTrivial

abbrev RelCnstrWithProof.satisfied (cₚ : RelCnstrWithProof) : GoalM LBool :=
  cₚ.c.satisfied

def RelCnstrWithProof.norm (cₚ : RelCnstrWithProof) : GoalM RelCnstrWithProof := do
  let cₚ ← if cₚ.c.isSorted then
    pure cₚ
  else
    mkRelCnstrWithProof cₚ.c.norm (.norm cₚ)
  let k := cₚ.c.gcdCoeffs
  if k != 1 then
    mkRelCnstrWithProof (cₚ.c.div k) (.divCoeffs cₚ)
  else
    return cₚ

def assertRelCnstr (cₚ : RelCnstrWithProof) : GoalM Unit := do
  if (← isInconsistent) then return ()
  let cₚ ← cₚ.norm
  if cₚ.isUnsat then
    trace[grind.cutsat.le.unsat] "{← cₚ.denoteExpr}"
    let hf ← withProofContext do
      return mkApp4 (mkConst ``Int.Linear.RelCnstr.false_of_isUnsat_of_denote) (← getContext) (toExpr cₚ.c) reflBoolTrue (← cₚ.toExprProof)
    closeGoal hf
  else if cₚ.isTrivial then
    trace[grind.cutsat.le.trivial] "{← cₚ.denoteExpr}"
    return ()
  else
    -- TODO
    return ()

private def reportNonNormalized (e : Expr) : GoalM Unit := do
  reportIssue! "unexpected non normalized inequality constraint found{indentExpr e}"

private def toRelCnstr? (e : Expr) : GoalM (Option RelCnstr) := do
  let_expr LE.le _ inst a b ← e | return none
  unless (← isInstLEInt inst) do return none
  let some k ← getIntValue? b
    | reportNonNormalized e; return none
  unless k == 0 do
    reportNonNormalized e; return none
  let p ← toPoly a
  return some <| .le p

/--
Given an expression `e` that is in `True` (or `False` equivalence class), if `e` is an
integer inequality, asserts it to the cutsat state.
-/
def propagateIfIntLe (e : Expr) (eqTrue : Bool) : GoalM Unit := do
  let some c ← toRelCnstr? e | return ()
  let cₚ ← if eqTrue then
    mkRelCnstrWithProof c (.expr (← mkOfEqTrue (← mkEqTrueProof e)))
  else
    mkRelCnstrWithProof (c.mul (-1) |>.addConst 1) (.notExpr (← mkOfEqFalse (← mkEqFalseProof e)))
  trace[grind.cutsat.assert.le] "{← cₚ.denoteExpr}"
  assertRelCnstr cₚ

end Lean.Meta.Grind.Arith.Cutsat
