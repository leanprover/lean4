/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types

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

private partial def satisfyDiseqs (goal : Goal) (a : Std.HashMap Expr Rat) (e : Expr) (v : Int) : Bool := Id.run do
  let some parents := goal.parents.find? { expr := e } | return true
  for parent in parents do
    let_expr Eq _ lhs rhs := parent | continue
    let some root := goal.getRoot? parent | continue
    if root.isConstOf ``False then
      let some lhsRoot := goal.getRoot? lhs | continue
      let some rhsRoot := goal.getRoot? rhs | continue
      if lhsRoot == e && !checkDiseq rhsRoot then return false
      if rhsRoot == e && !checkDiseq lhsRoot then return false
  return true
where
  checkDiseq (other : Expr) : Bool :=
    if let some v' := a[other]? then
      v' != v
    else
      true

private partial def pickUnusedValue (goal : Goal) (a : Std.HashMap Expr Rat) (e : Expr) (next : Int) (alreadyUsed : Std.HashSet Int) : Int :=
  go next
where
  go (next : Int) : Int :=
    if alreadyUsed.contains next then
      go (next+1)
    else if satisfyDiseqs goal a e next then
      next
    else
      go (next + 1)

private def isInterpretedTerm (e : Expr) : Bool :=
  isNatNum e || isIntNum e || e.isAppOf ``HAdd.hAdd || e.isAppOf ``HMul.hMul || e.isAppOf ``HSub.hSub
  || e.isAppOf ``Neg.neg || e.isAppOf ``HDiv.hDiv || e.isAppOf ``HMod.hMod
  || e.isAppOf ``NatCast.natCast || e.isIte || e.isDIte

private def natCast? (e : Expr) : Option Expr :=
  let_expr NatCast.natCast _ inst a := e | none
  let_expr instNatCastInt := inst | none
  some a

private def assignEqc (goal : Goal) (e : Expr) (v : Rat) (a : Std.HashMap Expr Rat) : Std.HashMap Expr Rat := Id.run do
  let mut a := a
  for e in goal.getEqc e do
    a := a.insert e v
  return a

private def getAssignment? (goal : Goal) (node : ENode) : MetaM (Option Rat) := do
  assert! isSameExpr node.self node.root
  if let some v := getCutsatAssignment? goal node then
    return some v
  else if let some v ← getIntValue? node.self then
    return some v
  else if let some v ← getNatValue? node.self then
    return some (Int.ofNat v)
  else
    return none

/--
Construct a model that statisfies all constraints in the cutsat model.
It also assigns values to integer terms that have not been internalized by the
cutsat model.

Remark: it uses rational numbers because cutsat may have failed to build an
integer model.
-/
def mkModel (goal : Goal) : MetaM (Array (Expr × Rat)) := do
  let mut used : Std.HashSet Int := {}
  let mut nextVal : Int := 0
  let mut model := {}
  let nodes := goal.getENodes
  -- Assign on expressions associated with cutsat terms or interpreted terms
  for node in nodes do
    if isSameExpr node.root node.self then
    if (← isIntNatENode node) then
      if let some v ← getAssignment? goal node then
        if v.den == 1 then used := used.insert v.num
        model := assignEqc goal node.self v model
  -- Assign cast terms
  for node in nodes do
    let i := node.self
    let some n := natCast? i | pure ()
    if model[n]?.isNone then
      let some v := model[i]? | pure ()
      model := assignEqc goal n v model
  -- Assign the remaining ones with values not used by cutsat
  for node in nodes do
    if isSameExpr node.root node.self then
    if (← isIntNatENode node) then
    if model[node.self]?.isNone then
      let v := pickUnusedValue goal model node.self nextVal used
      model := assignEqc goal node.self v model
      used := used.insert v
  let mut r := #[]
  for (e, v) in model do
    unless isInterpretedTerm e do
      r := r.push (e, v)
  r := r.qsort fun (e₁, _) (e₂, _) => e₁.lt e₂
  if (← isTracingEnabledFor `grind.cutsat.model) then
    for (x, v) in r do
      trace[grind.cutsat.model] "{quoteIfNotAtom x} := {v}"
  return r

end Lean.Meta.Grind.Arith.Cutsat
