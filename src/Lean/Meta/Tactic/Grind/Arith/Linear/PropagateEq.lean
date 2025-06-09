/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.CommRing.Poly
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Var
import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
import Lean.Meta.Tactic.Grind.Arith.Linear.Reify
import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Proof

namespace Lean.Meta.Grind.Arith.Linear
/-- Returns `some structId` if `a` and `b` are elements of the same structure. -/
private def inSameStruct? (a b : Expr) : GoalM (Option Nat) := do
  let some structId ← getTermStructId? a | return none
  let some structId' ← getTermStructId? b | return none
  unless structId == structId' do return none -- This can happen when we have heterogeneous equalities
  return structId

/--
Returns the linarith expression denoting the given Lean expression.
Recall that we compute the linarith expressions during internalization.
-/
private def toLinExpr? (e : Expr) : LinearM (Option LinExpr) := do
  let s ← getStruct
  if let some re := s.denote.find? { expr := e } then
    return some re
  else if let some x := s.varMap.find? { expr := e } then
    return some (.var x)
  else
    reportIssue! "failed to convert to linarith expression{indentExpr e}"
    return none

@[export lean_process_linarith_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  let some structId ← inSameStruct? a b | return ()
  LinearM.run structId do
    trace_goal[grind.linarith.assert] "{← mkEq a b}"
    let some la ← toLinExpr? a | return ()
    let some lb ← toLinExpr? b | return ()
    let p := (la.sub lb).norm
    match p with
    | .nil => trace_goal[grind.linarith.assert.trivial] "{← p.denoteExpr}"
    | .add .. =>
      let c₁ : IneqCnstr := { p, strict := false, h := .eq1 a b la lb }
      c₁.assert
      let p := p.mul (-1)
      let c₂ : IneqCnstr := { p, strict := false, h := .eq2 a b la lb }
      c₂.assert

@[export lean_process_linarith_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  trace[grind.linarith.assert] "{a} ≠ {b}"
  -- TODO

end Lean.Meta.Grind.Arith.Linear
