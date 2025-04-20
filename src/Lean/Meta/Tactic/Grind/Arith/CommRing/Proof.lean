/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr

namespace Lean.Meta.Grind.Arith.CommRing

/--
Returns a context of type `RArray α` containing the variables of the given ring.
`α` is the type of the ring.
-/
def toContextExpr (ringId : Nat) : GoalM Expr := do
  let ring ← getRing ringId
  if h : 0 < ring.vars.size then
    RArray.toExpr ring.type id (RArray.ofFn (ring.vars[·]) h)
  else
    RArray.toExpr ring.type id (RArray.leaf (mkApp ring.natCastFn (toExpr 0)))

private def mkLemmaPrefix (ringId : Nat) (declName declNameC : Name) : GoalM Expr := do
  let ring ← getRing ringId
  let ctx ← toContextExpr ringId
  if let some (charInst, c) ← nonzeroCharInst? ringId then
    return mkApp5 (mkConst declNameC [ring.u]) ring.type (toExpr c) ring.commRingInst charInst ctx
  else
    return mkApp3 (mkConst declName [ring.u]) ring.type ring.commRingInst ctx

def setNeUnsat (ringId : Nat) (a b : Expr) (ra rb : RingExpr) : GoalM Unit := do
  let h ← mkLemmaPrefix ringId ``Grind.CommRing.ne_unsat ``Grind.CommRing.ne_unsatC
  closeGoal <| mkApp4 h (toExpr ra) (toExpr rb) reflBoolTrue (← mkDiseqProof a b)

def setEqUnsat (ringId : Nat) (k : Int) (a b : Expr) (ra rb : RingExpr) : GoalM Unit := do
  let mut h ← mkLemmaPrefix ringId ``Grind.CommRing.eq_unsat ``Grind.CommRing.eq_unsatC
  let (charInst, c) ← getCharInst ringId
  if c == 0 then
    h := mkApp h charInst
  closeGoal <| mkApp5 h (toExpr ra) (toExpr rb) (toExpr k) reflBoolTrue (← mkEqProof a b)

end Lean.Meta.Grind.Arith.CommRing
