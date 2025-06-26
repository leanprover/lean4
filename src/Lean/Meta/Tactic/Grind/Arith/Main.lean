/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Arith.Offset
import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
import Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr
import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
import Lean.Meta.Tactic.Grind.Arith.Linear.Search

namespace Lean.Meta.Grind.Arith

namespace Offset
def isCnstr? (e : Expr) : GoalM (Option (Cnstr NodeId)) :=
  return (← get).arith.offset.cnstrs.find? { expr := e }

def assertTrue (c : Cnstr NodeId) (p : Expr) : GoalM Unit := do
  addEdge c.u c.v c.k (← mkOfEqTrue p)

def assertFalse (c : Cnstr NodeId) (p : Expr) : GoalM Unit := do
  let p := mkOfNegEqFalse (← get').nodes c p
  let c := c.neg
  addEdge c.u c.v c.k p

end Offset

builtin_grind_propagator propagateLE ↓LE.le := fun e => do
  if (← isEqTrue e) then
    if let some c ← Offset.isCnstr? e then
      Offset.assertTrue c (← mkEqTrueProof e)
    Cutsat.propagateIfSupportedLe e (eqTrue := true)
    Linear.propagateIneq e (eqTrue := true)
  else if (← isEqFalse e) then
    if let some c ← Offset.isCnstr? e then
      Offset.assertFalse c (← mkEqFalseProof e)
    Cutsat.propagateIfSupportedLe e (eqTrue := false)
    Linear.propagateIneq e (eqTrue := false)

builtin_grind_propagator propagateLT ↓LT.lt := fun e => do
  if (← isEqTrue e) then
    Linear.propagateIneq e (eqTrue := true)
  else if (← isEqFalse e) then
    Linear.propagateIneq e (eqTrue := false)

def check : GoalM Bool := do
  let c₁ ← Cutsat.check
  let c₂ ← CommRing.check
  let c₃ ← Linear.check
  if c₁ || c₂ || c₃ then
    processNewFacts
    return true
  else
    return false

end Lean.Meta.Grind.Arith
