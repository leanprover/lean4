/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Init.Grind.Order
namespace Lean.Meta.Grind.Order
/--
Returns `declName α leInst isPreorderInst`
-/
public def mkLePreorderPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type s.leInst s.isPreorderInst

/--
Returns `declName α leInst isPartialInst`
-/
def mkLePartialPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type s.leInst s.isPartialInst?.get!

/--
Returns `declName α leInst ltInst lawfulOrderLtInst`
-/
def mkLeLtPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type s.leInst s.ltInst?.get! s.lawfulOrderLTInst?.get!

/--
Returns `declName α leInst ltInst lawfulOrderLtInst isPreorderInst`
-/
def mkLeLtPreorderPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp (← mkLeLtPrefix declName) s.isPreorderInst

/--
Returns `declName α leInst ltInst lawfulOrderLtInst isLinearPreorderInst`
-/
public def mkLeLtLinearPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp (← mkLeLtPrefix declName) s.isLinearPreInst?.get!

/--
Returns `declName α leInst isLinearPreorderInst`
-/
public def mkLeLinearPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type s.leInst s.isLinearPreInst?.get!

/--
Returns `declName α leInst ltInst lawfulOrderLtInst isPreorderInst ringInst ordRingInst`
-/
public def mkOrdRingPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  let h ← mkLeLtPreorderPrefix declName
  return mkApp2 h s.ringInst?.get! s.orderedRingInst?.get!

/--
Returns `declName α leInst ltInst lawfulOrderLtInst isLinearPreorderInst ringInst ordRingInst`
-/
public def mkLinearOrdRingPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  let h ← mkLeLtLinearPrefix declName
  return mkApp2 h s.ringInst?.get! s.orderedRingInst?.get!

def mkTransCoreProof (u v w : Expr) (strict₁ strict₂ : Bool) (h₁ h₂ : Expr) : OrderM Expr := do
  let h ← match strict₁, strict₂ with
    | false, false => mkLePreorderPrefix ``Grind.Order.le_trans
    | false, true  => mkLeLtPreorderPrefix ``Grind.Order.le_lt_trans
    | true,  false => mkLeLtPreorderPrefix ``Grind.Order.lt_le_trans
    | true,  true  => mkLeLtPreorderPrefix ``Grind.Order.lt_trans
  return mkApp5 h u v w h₁ h₂

/--
Assume `p₁` is `{ w := u, k := k₁, proof := p₁ }` and `p₂` is `{ w := w, k := k₂, proof := p₂ }`
`p₁` is the proof for edge `u → w` and `p₂` the proof for edge `w -> v`.
Then, this function returns a proof for edge `u -> v`.

Remark: for orders that do not support offsets.
-/
def mkTransCore (p₁ : ProofInfo) (p₂ : ProofInfo) (v : NodeId) : OrderM ProofInfo := do
  let { w := u, k.strict := s₁, proof := h₁, .. } := p₁
  let { w, k.strict := s₂, proof := h₂, .. } := p₂
  let ns := (← getStruct).nodes
  let h ← mkTransCoreProof ns[u]! ns[w]! ns[v]! s₁ s₂ h₁ h₂
  return { w := p₁.w, k.strict := s₁ || s₂, proof := h }

def mkTransOffsetProof (u v w : Expr) (k₁ k₂ : Weight) (h₁ h₂ : Expr) : OrderM Expr := do
  let h ← match k₁.strict, k₂.strict with
    | false, false => mkOrdRingPrefix ``Grind.Order.le_trans_k
    | false, true  => mkOrdRingPrefix ``Grind.Order.le_lt_trans_k
    | true,  false => mkOrdRingPrefix ``Grind.Order.lt_le_trans_k
    | true,  true  => mkOrdRingPrefix ``Grind.Order.lt_trans_k
  let k  := k₁.k + k₂.k
  let h := mkApp6 h u v w (toExpr k₁.k) (toExpr k₂.k) (toExpr k)
  return mkApp3 h h₁ h₂ eagerReflBoolTrue

/--
Assume `p₁` is `{ w := u, k := k₁, proof := p₁ }` and `p₂` is `{ w := w, k := k₂, proof := p₂ }`
`p₁` is the proof for edge `u -(k₁)→ w` and `p₂` the proof for edge `w -(k₂)-> v`.
Then, this function returns a proof for edge `u -(k₁+k₂) -> v`.

Remark: for orders that support offsets.
-/
def mkTransOffset (p₁ : ProofInfo) (p₂ : ProofInfo) (v : NodeId) : OrderM ProofInfo := do
  let { w := u, k:= k₁, proof := h₁, .. } := p₁
  let { w, k := k₂, proof := h₂, .. } := p₂
  let ns := (← getStruct).nodes
  let h ← mkTransOffsetProof ns[u]! ns[w]! ns[v]! k₁ k₂ h₁ h₂
  return { w := p₁.w, k.k := k₁.k + k₂.k, k.strict := k₁.strict || k₂.strict, proof := h }

/--
Assume `p₁` is `{ w := u, k := k₁, proof := p₁ }` and `p₂` is `{ w := w, k := k₂, proof := p₂ }`
`p₁` is the proof for edge `u -(k₁)→ w` and `p₂` the proof for edge `w -(k₂)-> v`.
Then, this function returns a proof for edge `u -(k₁+k₂) -> v`.

Remark: if the order does not support offset `k₁` and `k₂` are zero.
-/
public def mkTrans (p₁ : ProofInfo) (p₂ : ProofInfo) (v : NodeId) : OrderM ProofInfo := do
  if (← isRing) then
    mkTransOffset p₁ p₂ v
  else
    mkTransCore p₁ p₂ v

def mkPropagateEqTrueProofCore (u v : Expr) (k : Weight) (huv : Expr) (k' : Weight) : OrderM Expr := do
  if k.strict == k'.strict then
    mkEqTrue huv
  else
    assert! k.strict && !k'.strict
    let h ← mkLeLtPrefix ``Grind.Order.le_eq_true_of_lt
    return mkApp3 h u v huv

def mkPropagateEqTrueProofOffset (u v : Expr) (k : Weight) (huv : Expr) (k' : Weight) : OrderM Expr := do
  let declName := match k'.strict, k.strict with
    | false, false => ``Grind.Order.le_eq_true_of_le_k
    | false, true  => ``Grind.Order.le_eq_true_of_lt_k
    | true,  false => ``Grind.Order.lt_eq_true_of_le_k
    | true,  true  => ``Grind.Order.lt_eq_true_of_lt_k
  let h ← mkOrdRingPrefix declName
  return mkApp6 h u v (toExpr k.k) (toExpr k'.k) eagerReflBoolTrue huv

/--
Given a path `u --(k)--> v` justified by proof `huv`,
construct a proof of `e = True` where `e` is a term corresponding to the edge `u --(k') --> v`
-/
public def mkPropagateEqTrueProof (u v : Expr) (k : Weight) (huv : Expr) (k' : Weight) : OrderM Expr := do
  if (← isRing) then
    mkPropagateEqTrueProofOffset u v k huv k'
  else
    mkPropagateEqTrueProofCore u v k huv k'

def mkPropagateSelfEqTrueProofOffset (u : Expr) (k : Weight) : OrderM Expr := do
  let declName := match k.strict with
    | false => ``Grind.Order.le_eq_true_k
    | true  => ``Grind.Order.lt_eq_true_k
  let h ← mkOrdRingPrefix declName
  return mkApp3 h u (toExpr k.k) eagerReflBoolTrue

def mkPropagateSelfEqTrueProofCore (u : Expr) : OrderM Expr := do
  let h ← mkLePreorderPrefix ``Grind.Order.le_eq_true
  return mkApp h u

/--
Constructs a proof of `e = True` where `e` is a term corresponding to the edge `u --(k) --> u`
with `k` non-negative
-/
public def mkPropagateSelfEqTrueProof (u : Expr) (k : Weight) : OrderM Expr := do
  if (← isRing) then
    mkPropagateSelfEqTrueProofOffset u k
  else
    assert! !k.strict
    mkPropagateSelfEqTrueProofCore u

/--
`u < v → (v ≤ u) = False
-/
def mkPropagateEqFalseProofCore (u v : Expr) (k : Weight) (huv : Expr) (k' : Weight) : OrderM Expr := do
  let declName := match k'.strict, k.strict with
    | false, false => unreachable!
    | false, true  => ``Grind.Order.le_eq_false_of_lt
    | true,  false => ``Grind.Order.lt_eq_false_of_le
    | true,  true  => ``Grind.Order.lt_eq_false_of_lt
  let h ← mkLeLtPreorderPrefix declName
  return mkApp3 h u v huv

def mkPropagateEqFalseProofOffset (u v : Expr) (k : Weight) (huv : Expr) (k' : Weight) : OrderM Expr := do
  let declName := match k'.strict, k.strict with
    | false, false => ``Grind.Order.le_eq_false_of_le_k
    | false, true  => ``Grind.Order.le_eq_false_of_lt_k
    | true,  false => ``Grind.Order.lt_eq_false_of_le_k
    | true,  true  => ``Grind.Order.lt_eq_false_of_lt_k
  let h ← mkOrdRingPrefix declName
  return mkApp6 h u v (toExpr k.k) (toExpr k'.k) eagerReflBoolTrue huv

/--
Given a path `u --(k)--> v` justified by proof `huv`,
construct a proof of `e = False` where `e` is a term corresponding to the edge `u --(k') --> v`
-/
public def mkPropagateEqFalseProof (u v : Expr) (k : Weight) (huv : Expr) (k' : Weight) : OrderM Expr := do
  if (← isRing) then
    mkPropagateEqFalseProofOffset u v k huv k'
  else
    mkPropagateEqFalseProofCore u v k huv k'

def mkPropagateSelfEqFalseProofOffset (u : Expr) (k : Weight) : OrderM Expr := do
  let declName := match k.strict with
    | false => ``Grind.Order.le_eq_false_k
    | true  => ``Grind.Order.lt_eq_false_k
  let h ← mkOrdRingPrefix declName
  return mkApp3 h u (toExpr k.k) eagerReflBoolTrue

def mkPropagateSelfEqFalseProofCore (u : Expr) : OrderM Expr := do
  let h ← mkLeLtPrefix ``Grind.Order.lt_eq_false
  return mkApp h u

/--
Constructs a proof of `e = False` where `e` is a term corresponding to the edge `u --(k) --> u` and
`k` is negative.
-/
public def mkPropagateSelfEqFalseProof (u : Expr) (k : Weight) : OrderM Expr := do
  if (← isRing) then
    mkPropagateSelfEqFalseProofOffset u k
  else
    assert! k.strict
    mkPropagateSelfEqFalseProofCore u

def mkSelfUnsatProofCore (u : Expr) (h : Expr) : OrderM Expr := do
  let hf ← mkLeLtPreorderPrefix ``Grind.Order.lt_unsat
  return mkApp2 hf u h

def mkSelfUnsatProofOffset (u : Expr) (k : Weight) (h : Expr) : OrderM Expr := do
  let declName := if k.strict then
    ``Grind.Order.lt_unsat_k
  else
    ``Grind.Order.le_unsat_k
  let hf ← mkOrdRingPrefix declName
  return mkApp4 hf u (toExpr k.k) eagerReflBoolTrue h

/--
Returns a proof of `False` using
`u --(k)--> u` with proof `h` where `k` is negative
-/
public def mkSelfUnsatProof (u : Expr) (k : Weight) (h : Expr) : OrderM Expr := do
  if (← isRing) then
    mkSelfUnsatProofOffset u k h
  else
    mkSelfUnsatProofCore u h

def mkUnsatProofCore (u v : Expr) (k₁ : Weight) (h₁ : Expr) (k₂ : Weight) (h₂ : Expr) : OrderM Expr := do
  let h ← mkTransCoreProof u v u k₁.strict k₂.strict h₁ h₂
  assert! k₁.strict || k₂.strict
  let hf ← mkLeLtPreorderPrefix ``Grind.Order.lt_unsat
  return mkApp2 hf u h

def mkUnsatProofOffset (u v : Expr) (k₁ : Weight) (h₁ : Expr) (k₂ : Weight) (h₂ : Expr) : OrderM Expr := do
  let h ← mkTransOffsetProof u v u k₁ k₂ h₁ h₂
  let declName := if k₁.strict || k₂.strict then
    ``Grind.Order.lt_unsat_k
  else
    ``Grind.Order.le_unsat_k
  let hf ← mkOrdRingPrefix declName
  return mkApp4 hf u (toExpr (k₁.k + k₂.k)) eagerReflBoolTrue h

/--
Returns a proof of `False` using a negative cycle composed of
- `u --(k₁)--> v` with proof `h₁`
- `v --(k₂)--> u` with proof `h₂`
-/
public def mkUnsatProof (u v : Expr) (k₁ : Weight) (h₁ : Expr) (k₂ : Weight) (h₂ : Expr) : OrderM Expr := do
  if (← isRing) then
    mkUnsatProofOffset u v k₁ h₁ k₂ h₂
  else
    mkUnsatProofCore u v k₁ h₁ k₂ h₂

public def mkEqProofOfLeOfLeCore (u v : Expr) (h₁ : Expr) (h₂ : Expr) : OrderM Expr := do
  let h ← mkLePartialPrefix ``Grind.Order.eq_of_le_of_le
  return mkApp4 h u v h₁ h₂

public def mkEqProofOfLeOfLeOffset (u v : Expr) (h₁ : Expr) (h₂ : Expr) : OrderM Expr := do
  let h ← mkLePartialPrefix ``Grind.Order.eq_of_le_of_le_0
  let h := mkApp h (← getStruct).ringInst?.get!
  return mkApp4 h u v h₁ h₂

public def mkEqProofOfLeOfLe (u v : Expr) (h₁ : Expr) (h₂ : Expr) : OrderM Expr := do
  if (← isRing) then
    mkEqProofOfLeOfLeOffset  u v h₁ h₂
  else
    mkEqProofOfLeOfLeCore u v h₁ h₂

end Lean.Meta.Grind.Order
