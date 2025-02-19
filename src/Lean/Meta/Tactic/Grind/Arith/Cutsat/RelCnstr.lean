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

def assertRelCnstr (_cₚ : RelCnstrWithProof) : GoalM Unit := do
  -- TODO
  return ()

private def reportNonNormalized (e : Expr) : GoalM Unit := do
  reportIssue! "unexpected non normalized inequality constraint found{indentExpr e}"

builtin_grind_propagator propagateLe ↓LE.le := fun e => do
  let_expr LE.le _ inst a b ← e | return ()
  unless (← isInstLEInt inst) do return ()
  let some k ← getIntValue? b
    | reportNonNormalized e; return ()
  unless k == 0 do
    reportNonNormalized e; return ()
  if (← isEqTrue e) then
    let p ← toPoly a
    let cₚ ← mkRelCnstrWithProof (.le p) (.expr (← mkOfEqTrue (← mkEqTrueProof e)))
    trace[grind.cutsat.assert.le] "{← cₚ.denoteExpr}"
    assertRelCnstr cₚ
  else if (← isEqFalse e) then
    /-
    TODO: negate
    -/
    return ()

end Lean.Meta.Grind.Arith.Cutsat
