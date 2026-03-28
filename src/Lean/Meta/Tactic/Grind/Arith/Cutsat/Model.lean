/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
import Lean.Meta.Tactic.Grind.Arith.ModelUtil
public section
namespace Lean.Meta.Grind.Arith.Cutsat

private def isIntNatENode (n : ENode) : MetaM Bool :=
  withDefault do
    let type ← inferType n.self
    isDefEq type Int.mkType
    <||>
    isDefEq type Nat.mkType

private def getCutsatAssignment? (goal : Goal) (node : ENode) : IO (Option Rat) := do
  assert! isSameExpr node.self node.root
  let some e := cutsatExt.getTerm node | return none
  let s ← cutsatExt.getStateCore goal
  let some x := s.varMap.find? { expr := e } | return none
  if h : x < s.assignment.size then
    return s.assignment[x]
  else
    return none

private def natCastToInt? (e : Expr) : Option Expr :=
  match_expr e with
  | NatCast.natCast _ inst a =>
    let_expr instNatCastInt := inst | none
    some a
  | Grind.ToInt.toInt _ _ _ a => some a
  | _ => none

def getAssignment? (goal : Goal) (e : Expr) : MetaM (Option Rat) := do
  let node ← goal.getENode (← goal.getRoot e)
  if let some v ← getCutsatAssignment? goal node then
    return some v
  else if let some v ← getIntValue? node.self then
    return some v
  else if let some v ← getNatValue? node.self then
    return some (Int.ofNat v)
  else
    return none

/--
Construct a model that satisfies all constraints in the cutsat model.
It also assigns values to integer terms that have not been internalized by the
cutsat model.

Remark: it uses rational numbers because cutsat may have failed to build an
integer model.
-/
def mkModel (goal : Goal) : MetaM (Array (Expr × Rat)) := do
  let mut model := {}
  -- Assign on expressions associated with cutsat terms or interpreted terms
  for e in goal.exprs do
    let node ← goal.getENode e
    if node.isRoot then
    if (← isIntNatENode node) then
      if let some v ← getAssignment? goal node.self then
        model := assignEqc goal node.self v model
  -- Assign natCast and toInt terms
  for e in goal.exprs do
    let node ← goal.getENode e
    let i := node.self
    let some n := natCastToInt? i | pure ()
    if model[n]?.isNone then
      let some v := model[i]? | pure ()
      model := assignEqc goal n v model
  let r ← finalizeModel goal isIntNatENode model
  traceModel `grind.lia.model r
  return r

end Lean.Meta.Grind.Arith.Cutsat
