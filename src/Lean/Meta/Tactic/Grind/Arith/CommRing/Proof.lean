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
structure PreNullCert where
  qs : Array Poly
  /--
  We don't use rational coefficients in the polynomials.
  Thus, we need to track a denominator to justify the proof step `div`.
  -/
  d  : Int := 1

def PreNullCert.unit (i : Nat) (n : Nat) : PreNullCert :=
  let qs := Array.replicate n (.num 0)
  let qs := qs.set! i (.num 1)
  { qs }

def PreNullCert.mul (c : PreNullCert) (k : Int) (char? : Option Nat) : PreNullCert :=
  if k == 1 then c
  else
    let g := Int.gcd k c.d
    let k := k / g
    let d := c.d / g
    if k == 1 then
      { c with d }
    else
      let qs := c.qs.map fun q => if q.isZero then q else q.mulConst' k char?
      { qs, d }

def PreNullCert.combine (k₁ : Int) (m₁ : Mon) (c₁ : PreNullCert) (k₂ : Int) (m₂ : Mon) (c₂ : PreNullCert) (char? : Option Nat) : PreNullCert := Id.run do
  let d₁    := c₁.d
  let d₂    := c₂.d
  let k₁_d₂ := k₁*d₂
  let k₂_d₁ := k₂*d₁
  let d₁_d₂ := d₁*d₂
  let g     := Int.gcd (Int.gcd k₁_d₂ k₂_d₁) d₁_d₂
  let k₁    := k₁_d₂ / g
  let k₂    := k₂_d₁ / g
  let d     := d₁_d₂ / g
  let qs₁   := c₁.qs
  let qs₂   := c₂.qs
  let n := Nat.max qs₁.size qs₂.size
  let mut qs : Vector Poly n := Vector.replicate n (.num 0)
  for h : i in [:n] do
    if h₁ : i < qs₁.size then
      let q₁ := qs₁[i].mulMon' k₁ m₁ char?
      if h₂ : i < qs₂.size then
        let q₂ := qs₂[i].mulMon' k₂ m₂ char?
        qs := qs.set i (q₁.combine' q₂ char?)
      else
        qs := qs.set i q₁
    else
      have : i < n := h.upper
      have : qs₁.size = n ∨ qs₂.size = n := by simp +zetaDelta [Nat.max_def]; split <;> simp [*]
      have : i < qs₂.size := by omega
      let q₂ := qs₂[i].mulMon' k₂ m₂ char?
      qs := qs.set i q₂
  return { qs := qs.toArray, d }

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
