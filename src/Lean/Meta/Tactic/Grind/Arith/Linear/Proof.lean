/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.Linear.Util
import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr

namespace Lean.Meta.Grind.Arith.Linear

open CommRing (RingExpr)

/--
Returns a context of type `RArray α` containing the variables of the given structure, where
`α` is `(← getStruct).type`.
-/
def toContextExpr : LinearM Expr := do
  let struct ← getStruct
  if h : 0 < struct.vars.size then
    RArray.toExpr struct.type id (RArray.ofFn (struct.vars[·]) h)
  else
    RArray.toExpr struct.type id (RArray.leaf struct.zero)

/--
Similar to `toContextExpr`, but for the `CommRing` module.
Recall that this module interfaces with the `CommRing` module and their variable contexts
may not be necessarily identical. For example, for this module, the term `x*y` does not have an interpretation
and we have a "variable" representing it, but it is interpreted in the `CommRing` module, and such
variable does not exist there. On the other direction, suppose we have the inequality `z < 0`, and
`z` does not occur in any equality or disequality. Then, the `CommRing` does not even "see" `z`, and
`z` does not occur in its context, but it occurs in the variable context created by this module.
-/
def toRingContextExpr : LinearM Expr := do
  withRingM do CommRing.toContextExpr

structure ProofM.State where
  cache       : Std.HashMap UInt64 Expr := {}
  polyMap     : Std.HashMap Poly Expr := {}
  exprMap     : Std.HashMap LinExpr Expr := {}
  ringExprMap : Std.HashMap RingExpr Expr := {}

structure ProofM.Context where
  ctx     : Expr
  ringCtx : Expr

/-- Auxiliary monad for constructing linarith proofs. -/
abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State LinearM)

/-- Returns a Lean expression representing the variable context used to construct linarith proofs. -/
private abbrev getContext : ProofM Expr := do
  return (← read).ctx

/--
Returns a Lean expression representing the auxiliary `CommRing` variable context
used to construct linarith proofs.
-/
private abbrev getRingContext : ProofM Expr := do
  return (← read).ringCtx

private abbrev caching (c : α) (k : ProofM Expr) : ProofM Expr := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if let some h := (← get).cache[addr]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert addr h }
    return h

def mkPolyDecl (p : Poly) : ProofM Expr := do
  if let some x := (← get).polyMap[p]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with polyMap := s.polyMap.insert p x }
  return x

def mkExprDecl (e : LinExpr) : ProofM Expr := do
  if let some x := (← get).exprMap[e]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with exprMap := s.exprMap.insert e x }
  return x

def mkRingExprDecl (e : RingExpr) : ProofM Expr := do
  if let some x := (← get).ringExprMap[e]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with ringExprMap := s.ringExprMap.insert e x }
  return x

private abbrev withProofContext (x : ProofM Expr) : LinearM Expr := do
  let struct ← getStruct
  withLetDecl `ctx  (mkApp (mkConst ``RArray [struct.u]) struct.type) (← toContextExpr) fun ctx => do
  withLetDecl `rctx (mkApp (mkConst ``RArray [struct.u]) struct.type) (← toRingContextExpr) fun ringCtx =>
  go { ctx, ringCtx } |>.run' {}
where
  go : ProofM Expr := do
    let h ← x
    let h ← mkLetOfMap (← get).polyMap h `p (mkConst ``Grind.Linarith.Poly) toExpr
    let h ← mkLetOfMap (← get).exprMap h `e (mkConst ``Grind.Linarith.Expr) toExpr
    let h ← mkLetOfMap (← get).ringExprMap h `r (mkConst ``Grind.CommRing.Expr) toExpr
    mkLetFVars #[(← getContext), (← getRingContext)] h

mutual
partial def EqCnstr.toExprProof (c' : EqCnstr) : ProofM Expr := caching c' do
  throwError "NIY"

partial def IneqCnstr.toExprProof (c' : IneqCnstr) : ProofM Expr := caching c' do
  throwError "NIY"

partial def DiesqCnstr.toExprProof (c' : DiseqCnstr) : ProofM Expr := caching c' do
  throwError "NIY"

partial def NotIneqCnstr.toExprProof (c' : NotIneqCnstr) : ProofM Expr := caching c' do
  throwError "NIY"

partial def UnsatProof.toExprProofCore (_h : UnsatProof) : ProofM Expr := do
  throwError "NIY"
end

def UnsatProof.toExprProof (h : UnsatProof) : LinearM Expr := do
  withProofContext do h.toExprProofCore

def setInconsistent (h : UnsatProof) : LinearM Unit := do
  if (← getStruct).caseSplits then
    -- Let the search procedure in `SearchM` resolve the conflict.
    modifyStruct fun s => { s with conflict? := some h }
  else
    let h ← h.toExprProof
    closeGoal h

end Lean.Meta.Grind.Arith.Linear
