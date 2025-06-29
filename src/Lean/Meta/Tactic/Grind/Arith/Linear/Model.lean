/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.Arith.ModelUtil

namespace Lean.Meta.Grind.Arith.Linear

def getAssignment? (s : Struct) (e : Expr) : Option Rat := Id.run do
  let some x := s.varMap.find? { expr := e } | return none
  if h : x < s.assignment.size then
    return some s.assignment[x]
  else
    return none

private def hasType (type : Expr) (n : ENode): MetaM Bool :=
  withDefault do
    let type' ← inferType n.self
    isDefEq type' type

/--
Construct a model that satisfies all constraints in the linarith model for the structure with id `structId`.
It also assigns values to (integer) terms that have not been internalized by the linarith model.
-/
def mkModel (goal : Goal) (structId : Nat) : MetaM (Array (Expr × Rat)) := do
  let mut model := {}
  let s := goal.arith.linear.structs[structId]!
  -- Assign on expressions associated with cutsat terms or interpreted terms
  for e in goal.exprs do
    let node ← goal.getENode e
    if node.isRoot then
    if (← hasType s.type node) then
      if let some v := getAssignment? s node.self then
        model := assignEqc goal node.self v model
  let r ← finalizeModel goal (hasType s.type) model
  traceModel `grind.linarith.model r
  return r

end Lean.Meta.Grind.Arith.Linear
