/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.ModelUtil


namespace Lean.Meta.Grind.Arith.Cutsat

private def isIntNatENode (n : ENode) : MetaM Bool :=
  withDefault do
    let type ← inferType n.self
    isDefEq type Int.mkType
    <||>
    isDefEq type Nat.mkType

private def getCutsatAssignment? (goal : Goal) (node : ENode) : Option Rat := Id.run do
  assert! isSameExpr node.self node.root
  let some e := node.cutsat? | return none
  let some x := goal.arith.cutsat.varMap.find? { expr := e } | return none
  if h : x < goal.arith.cutsat.assignment.size then
    return goal.arith.cutsat.assignment[x]
  else
    return none

private def natCast? (e : Expr) : Option Expr :=
  let_expr NatCast.natCast _ inst a := e | none
  let_expr instNatCastInt := inst | none
  some a

def getAssignment? (goal : Goal) (e : Expr) : MetaM (Option Rat) := do
  let node ← goal.getENode (← goal.getRoot e)
  if let some v := getCutsatAssignment? goal node then
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
  let mut used : Std.HashSet Int := {}
  let mut nextVal : Int := 0
  let mut model := {}
  -- Assign on expressions associated with cutsat terms or interpreted terms
  for e in goal.exprs do
    let node ← goal.getENode e
    if node.isRoot then
    if (← isIntNatENode node) then
      if let some v ← getAssignment? goal node.self then
        if v.den == 1 then used := used.insert v.num
        model := assignEqc goal node.self v model
  -- Assign cast terms
  for e in goal.exprs do
    let node ← goal.getENode e
    let i := node.self
    let some n := natCast? i | pure ()
    if model[n]?.isNone then
      let some v := model[i]? | pure ()
      model := assignEqc goal n v model
  -- Assign the remaining ones with values not used by cutsat
  for e in goal.exprs do
    let node ← goal.getENode e
    if node.isRoot then
    if (← isIntNatENode node) then
    if model[node.self]?.isNone then
      let v := pickUnusedValue goal model node.self nextVal used
      model := assignEqc goal node.self v model
      used := used.insert v
  let mut r := #[]
  for (e, v) in model do
    unless isInterpretedTerm e do
      r := r.push (e, v)
  r := r.qsort fun (e₁, _) (e₂, _) =>
    let g₁ := goal.getGeneration e₁
    let g₂ := goal.getGeneration e₂
    if g₁ != g₂ then g₁ < g₂ else e₁.lt e₂
  if (← isTracingEnabledFor `grind.cutsat.model) then
    for (x, v) in r do
      trace[grind.cutsat.model] "{quoteIfArithTerm x} := {v}"
  return r

end Lean.Meta.Grind.Arith.Cutsat
