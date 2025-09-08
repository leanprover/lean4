/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Grind.PropagatorAttr
public import Lean.Meta.Tactic.Grind.Arith.Offset
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search
public import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr
public import Lean.Meta.Tactic.Grind.Arith.Linear.Search

public section

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
    Cutsat.propagateLe e (eqTrue := true)
    Linear.propagateIneq e (eqTrue := true)
  else if (← isEqFalse e) then
    if let some c ← Offset.isCnstr? e then
      Offset.assertFalse c (← mkEqFalseProof e)
    Cutsat.propagateLe e (eqTrue := false)
    Linear.propagateIneq e (eqTrue := false)

builtin_grind_propagator propagateLT ↓LT.lt := fun e => do
  if (← isEqTrue e) then
    Linear.propagateIneq e (eqTrue := true)
    Cutsat.propagateLt e (eqTrue := true)
  else if (← isEqFalse e) then
    Linear.propagateIneq e (eqTrue := false)
    Cutsat.propagateLt e (eqTrue := false)

def check : GoalM Bool := do
  let c₁ ← Cutsat.check
  let c₃ ← Linear.check
  if c₁ || c₃ then
    processNewFacts
    return true
  else
    return false

end Lean.Meta.Grind.Arith
