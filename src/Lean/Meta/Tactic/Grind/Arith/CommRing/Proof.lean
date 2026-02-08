/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId
public import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
public import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM
import Lean.Data.RArray
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.ProofUtil
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.VarRename
import Init.Data.Nat.Order
import Init.Data.Order.Lemmas
public section
namespace Lean.Meta.Grind.Arith.CommRing
/--
Returns a context of type `RArray α` containing the variables `vars` where
`α` is the type of the ring.
-/
private def toContextExpr [Monad m] [MonadLiftT MetaM m] [MonadCanon m] [MonadRing m] (vars : Array Expr) : m Expr := do
  let ring ← getRing
  if h : 0 < vars.size then
    RArray.toExpr ring.type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr ring.type id (RArray.leaf (mkApp (← getNatCastFn) (toExpr 0)))

private def toSContextExpr' [Monad m] [MonadLiftT MetaM m] [MonadCanon m] [MonadSemiring m] (vars : Array Expr) : m Expr := do
  let semiring ← getSemiring
  if h : 0 < vars.size then
    RArray.toExpr semiring.type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr semiring.type id (RArray.leaf (mkApp (← getNatCastFn') (toExpr 0)))

/-- Similar to `toContextExpr`, but for semirings. -/
private def toSContextExpr (semiringId : Nat) (vars : Array Expr) : RingM Expr := do
  SemiringM.run semiringId do toSContextExpr' vars

/-- Returns the multiplier `k` for the input polynomial. See comment at `PolyDerivation.step`. -/
def PolyDerivation.getMultiplier (d : PolyDerivation) : Int :=
  go d 1
where
  go (d : PolyDerivation) (acc : Int) : Int :=
    match d with
    | .input _ => acc
    | .step _ k₁ d .. => go d (k₁ * acc)
    | .normEq0 _ d .. => go d acc

private def throwNoNatZeroDivisors : RingM α := do
  throwError "`grind` internal error, `NoNatZeroDivisors` instance is needed, but it is not available for{indentExpr (← getRing).type}"

private def getPolyConst (p : Poly) : RingM Int := do
  let .num k := p
    | throwError "`grind` internal error, constant polynomial expected {indentExpr (← p.denoteExpr)}"
  return k

structure ProofM.State where
  cache       : Std.HashMap UInt64 Expr := {}
  polyDecls   : Std.HashMap Poly Expr := {}
  monDecls    : Std.HashMap Mon Expr := {}
  exprDecls   : Std.HashMap RingExpr Expr := {}
  sexprDecls  : Std.HashMap SemiringExpr Expr := {}

structure ProofM.Context where
  ctx   : Expr
  /-- Context for semiring variables if available -/
  sctx? : Option Expr

abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State RingM)

/-- Returns a Lean expression representing the variable context used to construct `CommRing` proof steps. -/
private abbrev getContext : ProofM Expr := do
  return (← read).ctx

/--
Returns a Lean expression representing the semiring variable context
used to construct `CommRing` proof steps.
-/
private abbrev getSContext : ProofM Expr := do
  let some sctx := (← read).sctx?
    | throwError "`grind` internal error, semiring context is not available"
  return sctx

private abbrev caching (c : α) (k : ProofM Expr) : ProofM Expr := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if let some h := (← get).cache[addr]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert addr h }
    return h

local macro "declare! " decls:ident a:ident : term =>
  `(do if let some x := (← get).$decls[$a]? then
         return x
       let x := mkFVar (← mkFreshFVarId);
       modify fun s => { s with $decls:ident := (s.$decls).insert $a x };
       return x)

private def mkPolyDecl (p : Poly) : ProofM Expr := do
  declare! polyDecls p

private def mkExprDecl (e : RingExpr) : ProofM Expr := do
  declare! exprDecls e

private def mkSExprDecl (e : SemiringExpr) : ProofM Expr := do
  declare! sexprDecls e

private def mkMonDecl (m : Mon) : ProofM Expr := do
  declare! monDecls m

private def mkStepBasicPrefix (declName : Name) : ProofM Expr := do
  let ctx ← getContext
  let ring ← getCommRing
  return mkApp3 (mkConst declName [ring.u]) ring.type ring.commRingInst ctx

private def mkStepPrefix (declName declNameC : Name) : ProofM Expr := do
  if let some (charInst, char) ← nonzeroCharInst? then
    let ctx ← getContext
    let ring ← getCommRing
    return mkApp5 (mkConst declNameC [ring.u]) ring.type (toExpr char) ring.commRingInst charInst ctx
  else
    mkStepBasicPrefix declName

private def getSemiringIdOf : RingM Nat := do
  let some semiringId := (← getCommRing).semiringId? | throwError "`grind` internal error, semiring is not available"
  return semiringId

private def getSemiringOf : RingM CommSemiring := do
  SemiringM.run (← getSemiringIdOf) do getCommSemiring

private def mkSemiringPrefix (declName : Name) : ProofM Expr := do
  let sctx ← getSContext
  let semiring ← getSemiringOf
  return mkApp3 (mkConst declName [semiring.u]) semiring.type semiring.semiringInst sctx

private def mkSemiringAddRightCancelPrefix (declName : Name) : ProofM Expr := do
  let sctx ← getSContext
  let semiring ← getSemiringOf
  let some addRightCancelInst ← SemiringM.run (← getSemiringIdOf) do getAddRightCancelInst?
    | throwError "`grind` internal error, `AddRightCancel` instance is not available"
  return mkApp4 (mkConst declName [semiring.u]) semiring.type semiring.semiringInst addRightCancelInst sctx

open Lean.Grind.CommRing in
partial def _root_.Lean.Meta.Grind.Arith.CommRing.EqCnstr.toExprProof (c : EqCnstr) : ProofM Expr := caching c do
  match c.h with
  | .core a b lhs rhs =>
    let h ← mkStepPrefix ``Stepwise.core ``Stepwise.coreC
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c.p) eagerReflBoolTrue (← mkEqProof a b)
  | .coreS a b sa sb ra rb =>
    let h' ← mkSemiringPrefix ``Grind.Ring.OfSemiring.of_eq
    let h' := mkApp3 h' (← mkSExprDecl sa) (← mkSExprDecl sb) (← mkEqProof a b)
    let h ← mkStepPrefix ``Stepwise.core ``Stepwise.coreC
    return mkApp5 h (← mkExprDecl ra) (← mkExprDecl rb) (← mkPolyDecl c.p) eagerReflBoolTrue h'
  | .superpose k₁ m₁ c₁ k₂ m₂ c₂ =>
    let h ← mkStepPrefix ``Stepwise.superpose ``Stepwise.superposeC
    return mkApp10 h
      (toExpr k₁) (← mkMonDecl m₁) (← mkPolyDecl c₁.p)
      (toExpr k₂) (← mkMonDecl m₂) (← mkPolyDecl c₂.p)
      (← mkPolyDecl c.p) eagerReflBoolTrue (← toExprProof c₁) (← toExprProof c₂)
  | .simp k₁ c₁ k₂ m₂ c₂ =>
    let h ← mkStepPrefix ``Stepwise.simp ``Stepwise.simpC
    return mkApp9 h
      (toExpr k₁) (← mkPolyDecl c₁.p)
      (toExpr k₂) (← mkMonDecl m₂) (← mkPolyDecl c₂.p)
      (← mkPolyDecl c.p) eagerReflBoolTrue (← toExprProof c₁) (← toExprProof c₂)
  | .mul k c₁ =>
    let h ← mkStepPrefix ``Stepwise.mul ``Stepwise.mulC
    return mkApp5 h (← mkPolyDecl c₁.p) (toExpr k) (← mkPolyDecl c.p) eagerReflBoolTrue (← toExprProof c₁)
  | .div k c₁ =>
    let h ← mkStepPrefix ``Stepwise.div ``Stepwise.divC
    let some nzInst ← noZeroDivisorsInst?
      | throwNoNatZeroDivisors
    return mkApp6 h nzInst (← mkPolyDecl c₁.p) (toExpr k) (← mkPolyDecl c.p) eagerReflBoolTrue (← toExprProof c₁)
  | .gcd a b c₁ c₂ =>
    let h ← mkStepBasicPrefix ``Grind.CommRing.eq_gcd
    return mkApp8 h (toExpr a) (toExpr b) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c.p)
      eagerReflBoolTrue (← toExprProof c₁) (← toExprProof c₂)
  | .numEq0 k c₁ c₂ =>
    let h ← mkStepBasicPrefix ``Grind.CommRing.eq_normEq0
    return mkApp7 h (toExpr k) (← mkPolyDecl c₁.p) (← mkPolyDecl c₂.p) (← mkPolyDecl c.p)
      eagerReflBoolTrue (← toExprProof c₁) (← toExprProof c₂)

open Lean.Grind.CommRing in
/--
Given a polynomial derivation, returns `(k, p₀, h)` where `h` is a proof that
`k*p₀ = d.p`
-/
private def derivToExprProof (d : PolyDerivation) : ProofM (Int × Poly × Expr) := do
  match d with
  | .input p₀ =>
    let h := mkApp (← mkStepBasicPrefix ``Stepwise.d_init) (← mkPolyDecl p₀)
    return (1, p₀, h)
  | .step p k₁ d k₂ m₂ c₂ =>
    let (k, p₀, h₁) ← derivToExprProof d
    let h₂ ← c₂.toExprProof
    let h ← if k₁ == 1 then
      mkStepPrefix ``Stepwise.d_step1 ``Stepwise.d_step1C
    else
      pure <| mkApp (← mkStepPrefix ``Stepwise.d_stepk ``Stepwise.d_stepkC) (toExpr k₁)
    let h := mkApp10 h
      (toExpr k) (← mkPolyDecl p₀) (← mkPolyDecl d.p)
      (toExpr k₂) (← mkMonDecl m₂) (← mkPolyDecl c₂.p) (← mkPolyDecl p)
      eagerReflBoolTrue h₁ h₂
    return (k₁*k, p₀, h)
  | .normEq0 p d c =>
    let (k, p₀, h₁) ← derivToExprProof d
    let h₂ ← c.toExprProof
    let .num a := c.p | unreachable!
    let h ← mkStepBasicPrefix ``Grind.CommRing.d_normEq0
    let h := mkApp9 h
      (toExpr k) (toExpr a.natAbs) (← mkPolyDecl p₀) (← mkPolyDecl d.p)
      (← mkPolyDecl c.p) (← mkPolyDecl p) eagerReflBoolTrue h₁ h₂
    return (k, p₀, h)

open Lean.Grind.CommRing in
/--
Given a derivation `d` for `k * p = 0` where `lhs - rhs = p`, returns a proof for `lhs = rhs`.
-/
private def mkImpEqExprProof (lhs rhs : RingExpr) (d : PolyDerivation) : ProofM Expr := do
  assert! d.p matches .num 0
  let (k, p₀, h₁) ← derivToExprProof d
  let h ← if k == 1 then
    mkStepPrefix ``Stepwise.imp_1eq ``Stepwise.imp_1eqC
  else
    let some nzInst ← noZeroDivisorsInst?
      | throwNoNatZeroDivisors
    pure <| mkApp2 (← mkStepPrefix ``Stepwise.imp_keq ``Stepwise.imp_keqC) nzInst (toExpr k)
  return mkApp6 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl p₀) (← mkPolyDecl d.p) eagerReflBoolTrue h₁

private def mkContext (h : Expr) : ProofM Expr := do
  let usedVars     :=
    collectMapVars (← get).monDecls (·.collectVars) >>
    collectMapVars (← get).polyDecls (·.collectVars) >>
    collectMapVars (← get).exprDecls (·.collectVars) <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getRing).vars
  let vars         := vars'.map fun x => vars[x]!
  let h := mkLetOfMap (← get).polyDecls h `p (mkConst ``Grind.CommRing.Poly) fun p => toExpr <| p.renameVars varRename
  let h := mkLetOfMap (← get).monDecls h `m (mkConst ``Grind.CommRing.Mon) fun m => toExpr <| m.renameVars varRename
  let h := mkLetOfMap (← get).exprDecls h `e (mkConst ``Grind.CommRing.Expr) fun e => toExpr <| e.renameVars varRename
  let h := h.abstract #[(← read).ctx]
  if h.hasLooseBVars then
    let ring ← getRing
    let ctxType := mkApp (mkConst ``RArray [ring.u]) ring.type
    let ctxVal ← toContextExpr vars
    return .letE `ctx ctxType ctxVal h (nondep := false)
  else
    return h

private def mkSemiringContext (h : Expr) : ProofM Expr := do
  let some sctx := (← read).sctx? | return h
  let some semiringId := (← getCommRing).semiringId? | return h
  let semiring ← getSemiringOf
  let usedVars     := collectMapVars (← get).sexprDecls (·.collectVars) {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := vars'.map fun x => semiring.vars[x]!
  let h := mkLetOfMap (← get).sexprDecls h `s (mkConst ``Grind.CommRing.Expr) fun s => toExpr <| s.renameVars varRename
  let h := h.abstract #[sctx]
  if h.hasLooseBVars then
    let ctxType := mkApp (mkConst ``RArray [semiring.u]) semiring.type
    let ctxVal ← toSContextExpr semiringId vars
    return .letE `sctx ctxType ctxVal h (nondep := false)
  else
    return h

private abbrev withProofContext (x : ProofM Expr) : RingM Expr := do
  let ctx := mkFVar (← mkFreshFVarId)
  let sctx? ← if (← getCommRing).semiringId?.isSome then pure <| some (mkFVar (← mkFreshFVarId)) else pure none
  go { ctx, sctx? } |>.run' {}
where
  go : ProofM Expr := do
    let h ← x
    let h ← mkContext h
    mkSemiringContext h

open Lean.Grind.CommRing in
def EqCnstr.setUnsat  (c : EqCnstr) : RingM Unit := do
  let h ← withProofContext do
    let ring ← getCommRing
    if let some (charInst, char) := ring.charInst? then
      let mut h ← mkStepPrefix ``Stepwise.unsat_eq ``Stepwise.unsat_eqC
      if char == 0 then
        h := mkApp h charInst
      let k ← getPolyConst c.p
      return mkApp4 h (← mkPolyDecl c.p) (toExpr k) eagerReflBoolTrue (← c.toExprProof)
    else if let some fieldInst := ring.fieldInst? then
      return mkApp6 (mkConst ``Grind.CommRing.one_eq_zero_unsat [ring.u]) ring.type fieldInst (← getContext)
        (← mkPolyDecl c.p) eagerReflBoolTrue (← c.toExprProof)
    else
      throwError "`grind ring` internal error, unexpected unsat eq proof {← c.denoteExpr}"
  closeGoal h

def DiseqCnstr.setUnsat (c : DiseqCnstr) : RingM Unit := do
  let h ← withProofContext do
    let heq ← mkImpEqExprProof c.rlhs c.rrhs c.d
    let hne ← if let some (sa, sb) := c.ofSemiring? then
      let h ← mkSemiringAddRightCancelPrefix ``Grind.Ring.OfSemiring.of_diseq
      pure <| mkApp3 h (← mkSExprDecl sa) (← mkSExprDecl sb) (← mkDiseqProof c.lhs c.rhs)
    else
      mkDiseqProof c.lhs c.rhs
    return mkApp hne heq
  closeGoal h

def propagateEq (a b : Expr) (ra rb : RingExpr) (d : PolyDerivation) : RingM Unit := do
  let heq ← withProofContext do
    mkImpEqExprProof ra rb d
  let ring ← getRing
  let eq := mkApp3 (mkConst ``Eq [.succ ring.u]) ring.type a b
  pushEq a b <| mkExpectedPropHint heq eq

/--
Given `a` and `b`, such that `a ≠ b` in the core and `sa` and `sb` their reified semiring
terms s.t. `sa.toPoly == sb.toPoly`, close the goal.
-/
def setSemiringDiseqUnsat (a b : Expr) (sa sb : SemiringExpr) : SemiringM Unit := do
  let semiring ← getCommSemiring
  let hne ← mkDiseqProof a b
  let usedVars     := sa.collectVars >> sb.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := (← getSemiring).vars
  let vars         := vars'.map fun x => vars[x]!
  let sa           := sa.renameVars varRename
  let sb           := sb.renameVars varRename
  let ctx          ← toSContextExpr' vars
  let h := mkApp3 (mkConst ``Grind.CommRing.eq_normS [semiring.u]) semiring.type semiring.commSemiringInst ctx
  let h := mkApp3 h (toExpr sa) (toExpr sb) eagerReflBoolTrue
  closeGoal (mkApp hne h)

/--
Given `a` and `b`, such that `a ≠ b` in the core and `ra` and `rb` their reified ring
terms s.t. `ra.toPoly_nc == rb.toPoly_nc`, close the goal.
-/
def setNonCommRingDiseqUnsat (a b : Expr) (ra rb : RingExpr) : NonCommRingM Unit := do
  let ring ← getRing
  let hne ← mkDiseqProof a b
  let usedVars     := ra.collectVars >> rb.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := ring.vars
  let vars         := vars'.map fun x => vars[x]!
  let ra           := ra.renameVars varRename
  let rb           := rb.renameVars varRename
  let ctx          ← toContextExpr vars
  let h := if let some (charInst, c) := ring.charInst? then
    mkApp5 (mkConst ``Grind.CommRing.Expr.eq_of_toPolyC_nc_eq [ring.u]) ring.type (toExpr c) ring.ringInst charInst ctx
  else
    mkApp3 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_nc_eq [ring.u]) ring.type ring.ringInst ctx
  let h := mkApp3 h (toExpr ra) (toExpr rb) eagerReflBoolTrue
  closeGoal (mkApp hne h)

/--
Given `a` and `b`, such that `a ≠ b` in the core and `sa` and `sb` their reified semiring
terms s.t. `sa.toPolyS_nc == sb.toPolyS_nc`, close the goal.
-/
def setNonCommSemiringDiseqUnsat (a b : Expr) (sa sb : SemiringExpr) : NonCommSemiringM Unit := do
  let semiring ← getSemiring
  let hne ← mkDiseqProof a b
  let usedVars     := sa.collectVars >> sb.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := semiring.vars
  let vars         := vars'.map fun x => vars[x]!
  let sa           := sa.renameVars varRename
  let sb           := sb.renameVars varRename
  let ctx          ← toSContextExpr' vars
  let h := mkApp3 (mkConst ``Grind.CommRing.eq_normS_nc [semiring.u]) semiring.type semiring.semiringInst ctx
  let h := mkApp3 h (toExpr sa) (toExpr sb) eagerReflBoolTrue
  closeGoal (mkApp hne h)

private structure NormResult where
  lhs  : RingExpr
  rhs  : RingExpr
  lhs' : RingExpr
  rhs' : RingExpr
  vars : Array Expr

private def norm (vars : PArray Expr) (lhs rhs lhs' rhs' : RingExpr) : NormResult :=
  let usedVars     := lhs.collectVars >> rhs.collectVars >> lhs'.collectVars >> rhs'.collectVars <| {}
  let vars'        := usedVars.toArray
  let varRename    := mkVarRename vars'
  let vars         := vars'.map fun x => vars[x]!
  let lhs          := lhs.renameVars varRename
  let rhs          := rhs.renameVars varRename
  let lhs'         := lhs'.renameVars varRename
  let rhs'         := rhs'.renameVars varRename
  { lhs, rhs, lhs', rhs', vars }

def mkLeIffProof (leInst ltInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, rhs, lhs', rhs', vars } := norm ring.vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp6 (mkConst ``Grind.CommRing.le_norm_expr [ring.u]) ring.type ring.commRingInst leInst ltInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let leFn := mkApp2 (mkConst ``LE.le [ring.u]) ring.type leInst
  let le   := mkApp2 leFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let le'  := mkApp2 leFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq le le'
  return mkExpectedPropHint h expected

def mkLtIffProof (leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, rhs, lhs', rhs', vars } := norm ring.vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp7 (mkConst ``Grind.CommRing.lt_norm_expr [ring.u]) ring.type ring.commRingInst leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let ltFn := mkApp2 (mkConst ``LT.lt [ring.u]) ring.type ltInst
  let lt   := mkApp2 ltFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let lt'  := mkApp2 ltFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq lt lt'
  return mkExpectedPropHint h expected

def mkEqIffProof (lhs rhs lhs' rhs' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, rhs, lhs', rhs', vars } := norm ring.vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.eq_norm_expr [ring.u]) ring.type ring.commRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let eq   := mkApp2 eqFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let eq'  := mkApp2 eqFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq eq eq'
  return mkExpectedPropHint h expected

/--
Given `e` and `e'` s.t. `e.toPoly == e'.toPoly`, returns a proof that `e.denote ctx = e'.denote ctx`
-/
def mkTermEqProof (e e' : RingExpr) : RingM Expr := do
  let ring ← getCommRing
  let { lhs, lhs', vars, .. } := norm ring.vars e (.num 0) e' (.num 0)
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_eq [ring.u]) ring.type ring.commRingInst
  let h := mkApp4 h ctx (toExpr lhs) (toExpr lhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let expected := mkApp2 eqFn (← lhs.denoteExpr' vars) (← lhs'.denoteExpr' vars)
  return mkExpectedPropHint h expected

def mkNonCommLeIffProof (leInst ltInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, rhs, lhs', rhs', vars } := norm ring.vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp6 (mkConst ``Grind.CommRing.le_norm_expr_nc [ring.u]) ring.type ring.ringInst leInst ltInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let leFn := mkApp2 (mkConst ``LE.le [ring.u]) ring.type leInst
  let le   := mkApp2 leFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let le'  := mkApp2 leFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq le le'
  return mkExpectedPropHint h expected

def mkNonCommLtIffProof (leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst : Expr) (lhs rhs lhs' rhs' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, rhs, lhs', rhs', vars } := norm ring.vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp7 (mkConst ``Grind.CommRing.lt_norm_expr_nc [ring.u]) ring.type ring.ringInst leInst ltInst lawfulOrdLtInst isPreorderInst orderedRingInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let ltFn := mkApp2 (mkConst ``LT.lt [ring.u]) ring.type ltInst
  let lt   := mkApp2 ltFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let lt'  := mkApp2 ltFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq lt lt'
  return mkExpectedPropHint h expected

def mkNonCommEqIffProof (lhs rhs lhs' rhs' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, rhs, lhs', rhs', vars } := norm ring.vars lhs rhs lhs' rhs'
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.eq_norm_expr_nc [ring.u]) ring.type ring.ringInst
  let h := mkApp6 h ctx (toExpr lhs) (toExpr rhs) (toExpr lhs') (toExpr rhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let eq   := mkApp2 eqFn (← lhs.denoteExpr' vars) (← rhs.denoteExpr' vars)
  let eq'  := mkApp2 eqFn (← lhs'.denoteExpr' vars) (← rhs'.denoteExpr' vars)
  let expected := mkPropEq eq eq'
  return mkExpectedPropHint h expected

/--
Given `e` and `e'` s.t. `e.toPoly_nc == e'.toPoly_nc`, returns a proof that `e.denote ctx = e'.denote ctx`
-/
def mkNonCommTermEqProof (e e' : RingExpr) : NonCommRingM Expr := do
  let ring ← getRing
  let { lhs, lhs', vars, .. } := norm ring.vars e (.num 0) e' (.num 0)
  let ctx ← toContextExpr vars
  let h := mkApp2 (mkConst ``Grind.CommRing.Expr.eq_of_toPoly_nc_eq [ring.u]) ring.type ring.ringInst
  let h := mkApp4 h ctx (toExpr lhs) (toExpr lhs') eagerReflBoolTrue
  let eqFn := mkApp (mkConst ``Eq [Level.succ ring.u]) ring.type
  let expected := mkApp2 eqFn (← lhs.denoteExpr' vars) (← lhs'.denoteExpr' vars)
  return mkExpectedPropHint h expected

end Lean.Meta.Grind.Arith.CommRing
