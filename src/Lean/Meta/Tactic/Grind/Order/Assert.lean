/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Init.Grind.Propagator
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Order.Util
import Lean.Meta.Tactic.Grind.Order.Proof
namespace Lean.Meta.Grind.Order
/--
Returns a proof for `u + k ≤ v` (or `u ≤ v + k`) where `k` is the
shortest path between `u` and `v`.
-/
partial def mkProofForPath (u v : NodeId) : OrderM Expr := do
  go (← getProof u v)
where
  go (p : ProofInfo) : OrderM Expr := do
    if u == p.w then
      return p.proof
    else
      let p' ← getProof u p.w
      go (← mkTrans p' p v)

/-- Adds `p` to the list of things to be propagated. -/
def pushToPropagate (p : ToPropagate) : OrderM Unit :=
  modifyStruct fun s => { s with propagate := p :: s.propagate }

/-
def propagateEqTrue (e : Expr) (u v : NodeId) (k k' : Int) : OrderM Unit := do
  let kuv ← mkProofForPath u v
  let u ← getExpr u
  let v ← getExpr v
  pushEqTrue e <| mkPropagateEqTrueProof u v k kuv k'

private def propagateEqFalse (e : Expr) (u v : NodeId) (k k' : Int) : OrderM Unit := do
  let kuv ← mkProofForPath u v
  let u ← getExpr u
  let v ← getExpr v
  pushEqFalse e <| mkPropagateEqFalseProof u v k kuv k'
-/

/--
Auxiliary function for implementing theory propagation.
Traverses the constraints `c` (representing an expression `e`) s.t.
`c.u = u` and `c.v = v`, it removes `c` from the list of constraints
associated with `(u, v)` IF
- `e` is already assigned, or
- `f c e` returns true
-/
@[inline]
private def updateCnstrsOf (u v : NodeId) (f : Cnstr NodeId → Expr → OrderM Bool) : OrderM Unit := do
  if let some cs := (← getStruct).cnstrsOf.find? (u, v) then
    let cs' ← cs.filterM fun (c, e) => do
      if (← isEqTrue e <||> isEqFalse e) then
        return false -- constraint was already assigned
      else
        return !(← f c e)
    modifyStruct fun s => { s with cnstrsOf := s.cnstrsOf.insert (u, v) cs' }

def assertTrue (c : Cnstr NodeId) (p : Expr) : OrderM Unit := do
  trace[grind.order.assert] "{p} = True: {← c.pp}"

def assertFalse (c : Cnstr NodeId) (p : Expr) : OrderM Unit := do
  trace[grind.order.assert] "{p} = False: {← c.pp}"

def getStructIdOf? (e : Expr) : GoalM (Option Nat) := do
  return (← get').exprToStructId.find? { expr := e }

builtin_grind_propagator propagateLE ↓LE.le := fun e => do
  let some structId ← getStructIdOf? e | return ()
  OrderM.run structId do
  let some c ← getCnstr? e | return ()
  if (← isEqTrue e) then
    assertTrue c e
  else if (← isEqFalse e) then
    assertFalse c e

end Lean.Meta.Grind.Order
