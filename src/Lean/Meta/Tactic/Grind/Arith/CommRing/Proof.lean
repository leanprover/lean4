/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr

namespace Lean.Meta.Grind.Arith.CommRing

/--
Returns a context of type `RArray α` containing the variables of the given ring.
`α` is the type of the ring.
-/
def toContextExpr : RingM Expr := do
  let ring ← getRing
  if h : 0 < ring.vars.size then
    RArray.toExpr ring.type id (RArray.ofFn (ring.vars[·]) h)
  else
    RArray.toExpr ring.type id (RArray.leaf (mkApp ring.natCastFn (toExpr 0)))

/--
A "pre" Nullstellensatz certificate.
Recall that, given the hypotheses `h₁ : lhs₁ = rhs₁` ... `hₙ : lhsₙ = rhsₙ`,
a Nullstellensatz certificate is of the form
```
q₁*(lhs₁ - rhs₁) + ... + qₙ*(lhsₙ - rhsₙ)
```
Each hypothesis is an `EqCnstr` justified by a `.core ..` `EqnCnstrProof`.
We dynamically associate them with unique indices based on the order we find them
during traversal.
For the other `EqCnstr`s we compute a "pre" certificate as a dense array
containing `q₁` ... `qₙ` needed to create the `EqCnstr`.

We are assuming the number of hypotheses used to derive a conclusion is small
and a dense array is a reasonable representation.
-/
abbrev PreNullCert := Array Poly

structure NullCertHypothesis where
  h   : Expr
  lhs : RingExpr
  rhs : RingExpr

structure ProofM.State where
  /-- Mapping from `EqCnstr` to `PreNullCert` -/
  cache       : Std.HashMap UInt64 PreNullCert := {}
  hypToId     : Std.HashMap UInt64 Nat := {}
  hyps        : Array NullCertHypothesis := #[]

private def mkLemmaPrefix (declName declNameC : Name) : RingM Expr := do
  let ring ← getRing
  let ctx ← toContextExpr
  if let some (charInst, c) ← nonzeroCharInst? then
    return mkApp5 (mkConst declNameC [ring.u]) ring.type (toExpr c) ring.commRingInst charInst ctx
  else
    return mkApp3 (mkConst declName [ring.u]) ring.type ring.commRingInst ctx

def setNeUnsat (a b : Expr) (ra rb : RingExpr) : RingM Unit := do
  let h ← mkLemmaPrefix ``Grind.CommRing.ne_unsat ``Grind.CommRing.ne_unsatC
  closeGoal <| mkApp4 h (toExpr ra) (toExpr rb) reflBoolTrue (← mkDiseqProof a b)

def setEqUnsat (k : Int) (a b : Expr) (ra rb : RingExpr) : RingM Unit := do
  let mut h ← mkLemmaPrefix ``Grind.CommRing.eq_unsat ``Grind.CommRing.eq_unsatC
  let (charInst, c) ← getCharInst
  if c == 0 then
    h := mkApp h charInst
  closeGoal <| mkApp5 h (toExpr ra) (toExpr rb) (toExpr k) reflBoolTrue (← mkEqProof a b)

def setInconsistent (c : EqCnstr) : RingM Unit := do
  trace_goal[grind.ring.assert.unsat] "{← c.denoteExpr}"
  -- TODO

end Lean.Meta.Grind.Arith.CommRing
