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
def mkLePreorderPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type s.leInst s.isPreorderInst

/--
Returns `declName α leInst ltInst lawfulOrderLtInst isPreorderInst`
-/
def mkLeLtPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [s.u]) s.type s.leInst s.ltInst?.get! s.lawfulOrderLTInst?.get! s.isPreorderInst

/--
Returns `declName α leInst ltInst lawfulOrderLtInst isPreorderInst ringInst ordRingInst`
-/
def mkOrdRingPrefix (declName : Name) : OrderM Expr := do
  let s ← getStruct
  let h ← mkLeLtPrefix declName
  return mkApp2 h s.ringInst?.get! s.orderedRingInst?.get!

/--
Assume `p₁` is `{ w := u, k := k₁, proof := p₁ }` and `p₂` is `{ w := w, k := k₂, proof := p₂ }`
`p₁` is the proof for edge `u → w` and `p₂` the proof for edge `w -> v`.
Then, this function returns a proof for edge `u -> v`.

Remark: for orders that do not support offsets.
-/
def mkTransCore (p₁ : ProofInfo) (p₂ : ProofInfo) (v : NodeId) : OrderM ProofInfo := do
  let { w := u, k.strict := s₁, proof := h₁, .. } := p₁
  let { w, k.strict := s₂, proof := h₂, .. } := p₂
  let h ← match s₁, s₂ with
    | false, false => mkLePreorderPrefix ``Grind.Order.le_trans
    | false, true  => mkLeLtPrefix ``Grind.Order.le_lt_trans
    | true,  false => mkLeLtPrefix ``Grind.Order.lt_le_trans
    | true,  true  => mkLeLtPrefix ``Grind.Order.lt_trans
  let ns := (← getStruct).nodes
  let h := mkApp5 h ns[u]! ns[w]! ns[v]! h₁ h₂
  return { w := p₁.w, k.strict := s₁ || s₂, proof := h }

/--
Assume `pi₁` is `{ w := u, k := k₁, proof := p₁ }` and `pi₂` is `{ w := w, k := k₂, proof := p₂ }`
`p₁` is the proof for edge `u -(k₁)→ w` and `p₂` the proof for edge `w -(k₂)-> v`.
Then, this function returns a proof for edge `u -(k₁+k₂) -> v`.

Remark: for orders that support offsets.
-/
def mkTransOffset (p₁ : ProofInfo) (p₂ : ProofInfo) (v : NodeId) : OrderM ProofInfo := do
  let { w := u, k.k := k₁, k.strict := s₁, proof := h₁, .. } := p₁
  let { w, k.k := k₂, k.strict := s₂, proof := h₂, .. } := p₂
  let h ← match s₁, s₂ with
    | false, false => mkOrdRingPrefix ``Grind.Order.le_trans_k
    | false, true  => mkOrdRingPrefix ``Grind.Order.le_lt_trans_k
    | true,  false => mkOrdRingPrefix ``Grind.Order.lt_le_trans_k
    | true,  true  => mkOrdRingPrefix ``Grind.Order.lt_trans_k
  let k  := k₁ + k₂
  let ns := (← getStruct).nodes
  let h := mkApp6 h ns[u]! ns[w]! ns[v]! (toExpr k₁) (toExpr k₂) (toExpr k)
  let h := mkApp3 h h₁ h₂ eagerReflBoolTrue
  return { w := p₁.w, k.k := k, k.strict := s₁ || s₂, proof := h }

/--
Assume `pi₁` is `{ w := u, k := k₁, proof := p₁ }` and `pi₂` is `{ w := w, k := k₂, proof := p₂ }`
`p₁` is the proof for edge `u -(k₁)→ w` and `p₂` the proof for edge `w -(k₂)-> v`.
Then, this function returns a proof for edge `u -(k₁+k₂) -> v`.

Remark: if the order does not support offset `k₁` and `k₂` are zero.
-/
public def mkTrans (p₁ : ProofInfo) (p₂ : ProofInfo) (v : NodeId) : OrderM ProofInfo := do
  let s ← getStruct
  if s.orderedRingInst?.isSome then
    mkTransOffset p₁ p₂ v
  else
    mkTransCore p₁ p₂ v

end Lean.Meta.Grind.Order
