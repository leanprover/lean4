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
def inSameStruct? (a b : Expr) : GoalM (Option Nat) := do
  let some structId ← getTermStructId? a | return none
  let some structId' ← getTermStructId? b | return none
  unless structId == structId' do return none -- This can happen when we have heterogeneous equalities
  return structId

private def processNewCommRingEq (a b : Expr) : LinearM Unit := do
  let some lhs ← withRingM <| CommRing.reify? a (skipVar := false) | return ()
  let some rhs ← withRingM <| CommRing.reify? b (skipVar := false) | return ()
  let gen := max (← getGeneration a) (← getGeneration b)
  let p' := (lhs.sub rhs).toPoly
  let lhs' ← p'.toIntModuleExpr gen
  let some lhs' ← reify? lhs' (skipVar := false) | return ()
  let p := lhs'.norm
  if p == .nil then return ()
  let c₁ : IneqCnstr := { p, strict := false, h := .ofCommRingEq a b lhs rhs p' lhs' }
  c₁.assert
  let p := p.mul (-1)
  let p' := p'.mulConst (-1)
  let lhs' ← p'.toIntModuleExpr gen
  let some lhs' ← reify? lhs' (skipVar := false) | return ()
  let c₂ : IneqCnstr := { p, strict := false, h := .ofCommRingEq b a rhs lhs p' lhs' }
  c₂.assert

private def processNewIntModuleEq (a b : Expr) : LinearM Unit := do
  let some lhs ← reify? a (skipVar := false) | return ()
  let some rhs ← reify? b (skipVar := false) | return ()
  let p := (lhs.sub rhs).norm
  if p == .nil then return ()
  let c₁ : IneqCnstr := { p, strict := false, h := .ofEq a b lhs rhs }
  c₁.assert
  let p := p.mul (-1)
  let c₂ : IneqCnstr := { p, strict := false, h := .ofEq b a rhs lhs }
  c₂.assert

@[export lean_process_linarith_eq]
def processNewEqImpl (a b : Expr) : GoalM Unit := do
  if isSameExpr a b then return () -- TODO: check why this is needed
  let some structId ← inSameStruct? a b | return ()
  LinearM.run structId do
    trace_goal[grind.linarith.assert] "{← mkEq a b}"
    if (← isCommRing) then
      processNewCommRingEq a b
    else
      processNewIntModuleEq a b

def DiseqCnstr.assert (c : DiseqCnstr) : LinearM Unit := do
  trace[grind.linarith.assert] "{← c.denoteExpr}"
  match c.p with
  | .nil =>
    trace[grind.linarith.unsat] "{← c.denoteExpr}"
    setInconsistent (.diseq c)
  | .add _ x _ =>
    trace[grind.linarith.assert.store] "{← c.denoteExpr}"
    modifyStruct fun s => { s with diseqs := s.diseqs.modify x (·.push c) }
    if (← c.satisfied) == .false then
      resetAssignmentFrom x

private def processNewCommRingDiseq (a b : Expr) : LinearM Unit := do
  let some lhs ← withRingM <| CommRing.reify? a (skipVar := false) | return ()
  let some rhs ← withRingM <| CommRing.reify? b (skipVar := false) | return ()
  let gen := max (← getGeneration a) (← getGeneration b)
  let p' := (lhs.sub rhs).toPoly
  let lhs' ← p'.toIntModuleExpr gen
  let some lhs' ← reify? lhs' (skipVar := false) | return ()
  let p := lhs'.norm
  let c : DiseqCnstr := { p, h := .coreCommRing a b lhs rhs p' lhs' }
  c.assert

private def processNewIntModuleDiseq (a b : Expr) : LinearM Unit := do
  let some lhs ← reify? a (skipVar := false) | return ()
  let some rhs ← reify? b (skipVar := false) | return ()
  let p := (lhs.sub rhs).norm
  let c : DiseqCnstr := { p, h := .core a b lhs rhs }
  c.assert

@[export lean_process_linarith_diseq]
def processNewDiseqImpl (a b : Expr) : GoalM Unit := do
  let some structId ← inSameStruct? a b | return ()
  LinearM.run structId do
    if (← isCommRing) then
      processNewCommRingDiseq a b
    else
      processNewIntModuleDiseq a b

end Lean.Meta.Grind.Arith.Linear
