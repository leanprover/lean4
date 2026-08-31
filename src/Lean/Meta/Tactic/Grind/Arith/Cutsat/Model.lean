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

/--
If `e` is a single embedding step — an accessor application (`Fin.val a`, `BitVec.toNat a`,
`BitVec.toInt a`) or a conversion to `BitVec` (`a.toBitVec`) — returns `a`. The value of `e`
determines the value of `a`. Unlike `isEmbeddingApp?`, chains such as `a.toBitVec.toNat` are
not collapsed; callers resolve them one step at a time.
-/
def embeddingArg? (e : Expr) : Option Expr :=
  match_expr e with
  | Fin.val _ a => some a
  | BitVec.toNat _ a => some a
  | BitVec.toInt _ a => some a
  | UInt8.toBitVec a => some a
  | UInt16.toBitVec a => some a
  | UInt32.toBitVec a => some a
  | UInt64.toBitVec a => some a
  | USize.toBitVec a => some a
  | Int8.toBitVec a => some a
  | Int16.toBitVec a => some a
  | Int32.toBitVec a => some a
  | Int64.toBitVec a => some a
  | ISize.toBitVec a => some a
  | _ => none

private def natCastToInt? (e : Expr) : Option Expr :=
  match_expr e with
  | NatCast.natCast _ inst a =>
    let_expr instNatCastInt := inst | none
    some a
  | _ => embeddingArg? e

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
  /-
  Assign `natCast` and embedding chains. Values flow from a term to its argument
  (`↑(a.toBitVec.toNat)` to `a.toBitVec.toNat` to `a.toBitVec` to `a`), and `goal.exprs` is in internalization order
  (subterms first), so the reverse traversal resolves the chains in one pass.
  -/
  for e in goal.exprs.toArray.reverse do
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
