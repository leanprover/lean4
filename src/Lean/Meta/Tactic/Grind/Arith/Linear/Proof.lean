/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.Linear.Util
import Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.DenoteExpr

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
  if (← isCommRing) then
    withRingM do CommRing.toContextExpr
  else
    let struct ← getStruct
    RArray.toExpr struct.type id (RArray.leaf struct.zero)

structure ProofM.State where
  cache       : Std.HashMap UInt64 Expr := {}
  polyMap     : Std.HashMap Poly Expr := {}
  exprMap     : Std.HashMap LinExpr Expr := {}
  ringPolyMap : Std.HashMap CommRing.Poly Expr := {}
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

def mkRingPolyDecl (p : CommRing.Poly) : ProofM Expr := do
  if let some x := (← get).ringPolyMap[p]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with ringPolyMap := s.ringPolyMap.insert p x }
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
    let h ← mkLetOfMap (← get).ringPolyMap h `rp (mkConst ``Grind.CommRing.Poly) toExpr
    let h ← mkLetOfMap (← get).ringExprMap h `re (mkConst ``Grind.CommRing.Expr) toExpr
    mkLetFVars #[(← getContext), (← getRingContext)] h

/--
Returns the prefix of a theorem with name `declName` where the first three arguments are
`{α} [IntModule α] (ctx : Context α)`
-/
private def mkIntModThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type s.intModuleInst (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first three arguments are
`{α} [IntModule α] [NoNatZeroDivisors α] (ctx : Context α)`
-/
private def mkIntModNoNatDivThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type s.intModuleInst (← getNoNatDivInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first four arguments are
`{α} [IntModule α] [Preorder α] (ctx : Context α)`
-/
private def mkIntModPreThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp4 (mkConst declName [s.u]) s.type s.intModuleInst (← getPreorderInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [IntModule α] [Preorder α] [IntModule.IsOrdered α] (ctx : Context α)`
This is the most common theorem prefix at `Linarith.lean`
-/
private def mkIntModPreOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [s.u]) s.type s.intModuleInst (← getPreorderInst) (← getIsOrdInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [IntModule α] [LinearOrder α] [IntModule.IsOrdered α] (ctx : Context α)`
This is the most common theorem prefix at `Linarith.lean`
-/
private def mkIntModLinOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [s.u]) s.type s.intModuleInst (← getLinearOrderInst) (← getIsOrdInst) (← getContext)

/--
Returns the prefix of a theorem with name `declName` where the first three arguments are
`{α} [CommRing α] (rctx : Context α)`
-/
private def mkCommRingThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp3 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [CommRing α] [Preorder α] [Ring.IsOrdered α] (rctx : Context α)`
-/
private def mkCommRingPreOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getPreorderInst) (← getRingIsOrdInst) (← getRingContext)

/--
Returns the prefix of a theorem with name `declName` where the first five arguments are
`{α} [CommRing α] [LinearOrder α] [Ring.IsOrdered α] (rctx : Context α)`
-/
private def mkCommRingLinOrdThmPrefix (declName : Name) : ProofM Expr := do
  let s ← getStruct
  return mkApp5 (mkConst declName [s.u]) s.type (← getCommRingInst) (← getLinearOrderInst) (← getRingIsOrdInst) (← getRingContext)

mutual
partial def IneqCnstr.toExprProof (c' : IneqCnstr) : ProofM Expr := caching c' do
  match c'.h with
  | .core e lhs rhs =>
    let h ← mkIntModPreOrdThmPrefix (if c'.strict then ``Grind.Linarith.lt_norm else ``Grind.Linarith.le_norm)
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) reflBoolTrue (mkOfEqTrueCore e (← mkEqTrueProof e))
  | .notCore e lhs rhs =>
    let h ← mkIntModLinOrdThmPrefix (if c'.strict then ``Grind.Linarith.not_le_norm else ``Grind.Linarith.not_lt_norm)
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) reflBoolTrue (mkOfEqFalseCore e (← mkEqFalseProof e))
  | .coreCommRing e lhs rhs p' lhs' =>
    let h' ← mkCommRingPreOrdThmPrefix (if c'.strict then ``Grind.CommRing.lt_norm else ``Grind.CommRing.le_norm)
    let h' := mkApp5 h' (← mkRingExprDecl lhs) (← mkRingExprDecl rhs) (← mkRingPolyDecl p') reflBoolTrue (mkOfEqTrueCore e (← mkEqTrueProof e))
    let h ← mkIntModPreOrdThmPrefix (if c'.strict then ``Grind.Linarith.lt_norm else ``Grind.Linarith.le_norm)
    return mkApp5 h (← mkExprDecl lhs') (← mkExprDecl .zero) (← mkPolyDecl c'.p) reflBoolTrue h'
  | .notCoreCommRing e lhs rhs p' lhs' =>
    let h' ← mkCommRingLinOrdThmPrefix (if c'.strict then ``Grind.CommRing.not_le_norm else ``Grind.CommRing.not_lt_norm)
    let h' := mkApp5 h' (← mkRingExprDecl lhs) (← mkRingExprDecl rhs) (← mkRingPolyDecl p') reflBoolTrue (mkOfEqFalseCore e (← mkEqFalseProof e))
    let h ← mkIntModPreOrdThmPrefix (if c'.strict then ``Grind.Linarith.lt_norm else ``Grind.Linarith.le_norm)
    return mkApp5 h (← mkExprDecl lhs') (← mkExprDecl .zero) (← mkPolyDecl c'.p) reflBoolTrue h'
  | .combine c₁ c₂ =>
    let (declName, c₁, c₂) :=
      match c₁.strict, c₂.strict with
      | true, true => (``Grind.Linarith.lt_lt_combine, c₁, c₂)
      | true, false => (``Grind.Linarith.le_lt_combine, c₂, c₁)
      | false, true => (``Grind.Linarith.le_lt_combine, c₁, c₂)
      | false, false => (``Grind.Linarith.le_le_combine, c₁, c₂)
    return mkApp6 (← mkIntModPreOrdThmPrefix declName) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) reflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .oneGtZero =>
    let s ← getStruct
    let h := mkApp5 (mkConst ``Grind.Linarith.zero_lt_one [s.u]) s.type (← getRingInst) (← getPreorderInst) (← getRingIsOrdInst) (← getContext)
    return mkApp3 h (← mkPolyDecl c'.p) reflBoolTrue (← mkEqRefl (← getOne))
  | .ofEq a b la lb =>
    let h ← mkIntModPreOrdThmPrefix ``Grind.Linarith.le_of_eq
    return mkApp5 h (← mkExprDecl la) (← mkExprDecl lb) (← mkPolyDecl c'.p) reflBoolTrue (← mkEqProof a b)
  | .ofCommRingEq a b la lb p' lhs' =>
    let h' ← mkCommRingThmPrefix ``Grind.CommRing.eq_norm
    let h' := mkApp5 h' (← mkRingExprDecl la) (← mkRingExprDecl lb) (← mkRingPolyDecl p') reflBoolTrue (← mkEqProof a b)
    let h ← mkIntModPreOrdThmPrefix ``Grind.Linarith.le_of_eq
    return mkApp5 h (← mkExprDecl lhs') (← mkExprDecl .zero) (← mkPolyDecl c'.p) reflBoolTrue h'
  | .dec h => return mkFVar h
  | .ofDiseqSplit c₁ fvarId h _ =>
    let hFalse ← h.toExprProofCore
    let lt ← getLtFn
    let hNot := mkLambda `h .default (mkApp2 lt (← c₁.p.denoteExpr) (← getZero)) (hFalse.abstract #[mkFVar fvarId])
    let h ← mkIntModLinOrdThmPrefix ``Grind.Linarith.diseq_split_resolve
    return mkApp5 h (← mkPolyDecl c₁.p) (← mkPolyDecl c'.p) reflBoolTrue (← c₁.toExprProof) hNot
  | _ => throwError "not implemented yet"

partial def DiseqCnstr.toExprProof (c' : DiseqCnstr) : ProofM Expr := caching c' do
  match c'.h with
  | .core a b lhs rhs =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.diseq_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) reflBoolTrue (← mkDiseqProof a b)
  | .coreCommRing a b lhs rhs p' lhs' =>
    let h' ← mkCommRingThmPrefix ``Grind.CommRing.diseq_norm
    let h' := mkApp5 h' (← mkRingExprDecl lhs) (← mkRingExprDecl rhs) (← mkRingPolyDecl p') reflBoolTrue (← mkDiseqProof a b)
    let h ← mkIntModThmPrefix ``Grind.Linarith.diseq_norm
    return mkApp5 h (← mkExprDecl lhs') (← mkExprDecl .zero) (← mkPolyDecl c'.p) reflBoolTrue h'
  | .neg c =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.diseq_neg
    return mkApp4 h (← mkPolyDecl c.p) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .subst k₁ k₂ c₁ c₂ =>
    let h ← mkIntModNoNatDivThmPrefix ``Grind.Linarith.eq_diseq_subst
    return mkApp8 h (toExpr k₁) (toExpr k₂) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p)
      reflBoolTrue (← c₁.toExprProof) (← c₂.toExprProof)
  | .subst1 k c₁ c₂ =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_diseq_subst1
    return mkApp7 h (toExpr k) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) reflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)
  | .oneNeZero => throwError "not implemented yet"

partial def EqCnstr.toExprProof (c' : EqCnstr) : ProofM Expr := caching c' do
  match c'.h with
  | .core a b lhs rhs =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_norm
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c'.p) reflBoolTrue (← mkEqProof a b)
  | .coreCommRing .. => throwError "not implemented yet"
  | .neg c =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_neg
    return mkApp4 h (← mkPolyDecl c.p) (← mkPolyDecl c'.p) reflBoolTrue (← c.toExprProof)
  | .coeff k c =>
    let h ← mkIntModNoNatDivThmPrefix ``Grind.Linarith.eq_coeff
    return mkApp5 h (← mkPolyDecl c.p) (← mkPolyDecl c'.p) (toExpr k) reflBoolTrue (← c.toExprProof)
  | .subst x c₁ c₂ =>
    let h ← mkIntModThmPrefix ``Grind.Linarith.eq_eq_subst
    return mkApp7 h (toExpr x) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c'.p) reflBoolTrue
      (← c₁.toExprProof) (← c₂.toExprProof)

partial def UnsatProof.toExprProofCore (h : UnsatProof) : ProofM Expr := do
  match h with
  | .lt c => return mkApp (← mkIntModPreThmPrefix ``Grind.Linarith.lt_unsat) (← c.toExprProof)
  | .diseq c => return mkApp (← mkIntModThmPrefix ``Grind.Linarith.diseq_unsat) (← c.toExprProof)

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

/-!
A linarith proof may depend on decision variables.
We collect them and perform non chronological backtracking.
-/
open CollectDecVars
mutual

partial def IneqCnstr.collectDecVars (c' : IneqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core .. | .notCore .. | .coreCommRing .. | .notCoreCommRing ..
  | .oneGtZero | .ofEq .. | .ofCommRingEq .. => return ()
  | .combine c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .norm c₁ _ => c₁.collectDecVars
  | .dec h => markAsFound h
  | .ofDiseqSplit (decVars := decVars) .. => decVars.forM markAsFound
  | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

-- `DiseqCnstr` is currently mutually recursive with `IneqCnstr`, but it will be in the future.
-- Actually, it cannot even contain decision variables in the current implementation.
partial def DiseqCnstr.collectDecVars (c' : DiseqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .core .. | .coreCommRing .. | .oneNeZero => return ()
  | .neg c => c.collectDecVars
  | .subst _ _ c₁ c₂ | .subst1 _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars

partial def EqCnstr.collectDecVars (c' : EqCnstr) : CollectDecVarsM Unit := do unless (← alreadyVisited c') do
  match c'.h with
  | .subst _ c₁ c₂ => c₁.collectDecVars; c₂.collectDecVars
  | .core .. | .coreCommRing .. => return ()
  | .neg c | .coeff _ c => c.collectDecVars

end

def UnsatProof.collectDecVars (h : UnsatProof) : CollectDecVarsM Unit := do
  match h with
  | .lt c | .diseq c => c.collectDecVars

end Lean.Meta.Grind.Arith.Linear
