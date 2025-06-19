/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Diseq
import Lean.Meta.Tactic.Grind.Arith.ProofUtil
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

def throwNoNatZeroDivisors : RingM α := do
  throwError "`grind` internal error, `NoNatZeroDivisors` instance is needed, but it is not available for{indentExpr (← getRing).type}"

def getPolyConst (p : Poly) : RingM Int := do
  let .num k := p
    | throwError "`grind` internal error, constant polynomial expected {indentExpr (← p.denoteExpr)}"
  return k

namespace Null
/-!
Proof term for a Nullstellensatz certificate.
-/

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
  deriving Inhabited

def PreNullCert.zero : PreNullCert :=
  { qs := #[] }

def PreNullCert.unit (i : Nat) (n : Nat) : PreNullCert :=
  let qs := Array.replicate n (.num 0)
  let qs := qs.set! i (.num 1)
  { qs }

def PreNullCert.div (c : PreNullCert) (k : Int) : RingM PreNullCert := do
  return { c with d := c.d * k }

def PreNullCert.mul (c : PreNullCert) (k : Int) : RingM PreNullCert := do
  if k == 1 then
    return c
  else
    let g := Int.gcd k c.d
    let k := k / g
    let d := c.d / g
    if k == 1 then
      return { c with d }
    else
      let qs ← c.qs.mapM fun q => q.mulConstM k
      return { qs, d }

def PreNullCert.combine (k₁ : Int) (m₁ : Mon) (c₁ : PreNullCert) (k₂ : Int) (m₂ : Mon) (c₂ : PreNullCert) : RingM PreNullCert := do
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
      let q₁ ← qs₁[i].mulMonM k₁ m₁
      if h₂ : i < qs₂.size then
        let q₂ ← qs₂[i].mulMonM k₂ m₂
        qs := qs.set i (← q₁.combineM q₂)
      else
        qs := qs.set i q₁
    else
      have : i < n := h.upper
      have : qs₁.size = n ∨ qs₂.size = n := by simp +zetaDelta only [Nat.max_def, right_eq_ite_iff]; split <;> simp [*]
      have : i < qs₂.size := by omega
      let q₂ ← qs₂[i].mulMonM k₂ m₂
      qs := qs.set i q₂
  return { qs := qs.toArray, d }

structure NullCertHypothesis where
  h   : Expr
  lhs : RingExpr
  rhs : RingExpr

structure ProofM.State where
  /-- Mapping from `EqCnstr` to `PreNullCert` -/
  cache       : Std.HashMap UInt64 PreNullCert := {}
  hyps        : Array NullCertHypothesis := #[]

abbrev ProofM := StateRefT ProofM.State RingM

private abbrev caching (c : α) (k : ProofM PreNullCert) : ProofM PreNullCert := do
  let addr := unsafe (ptrAddrUnsafe c).toUInt64 >>> 2
  if let some h := (← get).cache[addr]? then
    return h
  else
    let h ← k
    modify fun s => { s with cache := s.cache.insert addr h }
    return h

structure NullCertExt where
  d   : Int
  qhs : Array (Poly × NullCertHypothesis)

end Null

section
open Null
partial def EqCnstr.toPreNullCert (c : EqCnstr) : ProofM PreNullCert := caching c do
  match c.h with
  | .core a b lhs rhs =>
    let i := (← get).hyps.size
    let h ← mkEqProof a b
    modify fun s => { s with hyps := s.hyps.push { h, lhs, rhs } }
    return PreNullCert.unit i (i+1)
  | .superpose k₁ m₁ c₁ k₂ m₂ c₂ => (← c₁.toPreNullCert).combine k₁ m₁ k₂ m₂ (← c₂.toPreNullCert)
  | .simp k₁ c₁ k₂ m₂ c₂ => (← c₁.toPreNullCert).combine k₁ .unit k₂ m₂ (← c₂.toPreNullCert)
  | .mul k c => (← c.toPreNullCert).mul k
  | .div k c => (← c.toPreNullCert).div k

def PolyDerivation.toPreNullCert (d : PolyDerivation) : ProofM PreNullCert := do
  match d with
  | .input _ => return .zero
  | .step _p k₁ d k₂ m₂ c₂ =>
    -- Recall that _p = k₁*d.getPoly + k₂*m₂*c.p
    trace[grind.debug.ring.proof] ">> k₁: {k₁}, {(← d.toPreNullCert).d}, {(← c₂.toPreNullCert).d}"
    (← d.toPreNullCert).combine k₁ .unit (-k₂) m₂ (← c₂.toPreNullCert)

/-- Returns the multiplier `k` for the input polynomial. See comment at `PolyDerivation.step`. -/
def PolyDerivation.getMultiplier (d : PolyDerivation) : Int :=
  go d 1
where
  go (d : PolyDerivation) (acc : Int) : Int :=
    match d with
    | .input _ => acc
    | .step _ k₁ d .. => go d (k₁ * acc)

def EqCnstr.mkNullCertExt (c : EqCnstr) : RingM NullCertExt := do
  let (nc, s) ← c.toPreNullCert.run {}
  return { d := nc.d, qhs := nc.qs.zip s.hyps }

def PolyDerivation.mkNullCertExt (d : PolyDerivation) : RingM NullCertExt := do
  let (nc, s) ← d.toPreNullCert.run {}
  return { d := nc.d, qhs := nc.qs.zip s.hyps }

def DiseqCnstr.mkNullCertExt (c : DiseqCnstr) : RingM NullCertExt :=
  c.d.mkNullCertExt
end

namespace Null
def NullCertExt.toPoly (nc : NullCertExt) : RingM Poly := do
  let mut p : Poly := .num 0
  for (q, h) in nc.qhs do
    p ← p.combineM (← q.mulM (← (h.lhs.sub h.rhs).toPolyM))
  return p

def NullCertExt.check (c : EqCnstr) (nc : NullCertExt) : RingM Bool := do
  let p₁ := c.p.mulConst' nc.d (← nonzeroChar?)
  let p₂ ← nc.toPoly
  return p₁ == p₂

def NullCertExt.toNullCert (nc : NullCertExt) : Grind.CommRing.NullCert :=
  go nc.qhs.size .empty (by omega)
where
  go (i : Nat) (acc : Grind.CommRing.NullCert) (h : i ≤ nc.qhs.size) : Grind.CommRing.NullCert :=
    if h : i > 0 then
      let i := i - 1
      let (p, h) := nc.qhs[i]
      go i (.add p h.lhs h.rhs acc) (by omega)
    else
      acc

/--
Given a `pr`, returns `pr h₁ ... hₙ`, where `n` is size `nc.qhs.size`, and `hᵢ`s
are the equalities in the certificate.
-/
def NullCertExt.applyEqs (pr : Expr) (nc : NullCertExt) : Expr :=
  go 0 pr
where
  go (i : Nat) (pr : Expr) : Expr :=
    if _ : i < nc.qhs.size then
      let (_, h) := nc.qhs[i]
      go (i + 1) (mkApp pr h.h)
    else
      pr

private def getNoZeroDivInstIfNeeded? (k : Int) : RingM (Option Expr) := do
  if k == 1 then
    return none
  else
    let some inst ← noZeroDivisorsInst? | throwNoNatZeroDivisors
    return some inst

def setEqUnsat (c : EqCnstr) : RingM Unit := do
  trace_goal[grind.ring.assert.unsat] "{← c.denoteExpr}"
  let k ← getPolyConst c.p
  let ncx ← c.mkNullCertExt
  trace_goal[grind.ring.assert.unsat] "{ncx.d}*({← c.p.denoteExpr}), {← (← ncx.toPoly).denoteExpr}"
  let ring ← getRing
  let some (charInst, char) := ring.charInst?
    | throwError "`grind` internal error, `IsCharP` instance is needed, but it is not available for{indentExpr (← getRing).type}\nconsider not using `+ringNull`"
  let h := if char == 0 then
    mkApp (mkConst ``Grind.CommRing.NullCert.eq_unsat [ring.u]) ring.type
  else
    mkApp2 (mkConst ``Grind.CommRing.NullCert.eq_unsatC [ring.u]) ring.type (toExpr char)
  let ctx ← toContextExpr
  let nc := toExpr (ncx.toNullCert)
  let h := mkApp6 h ring.commRingInst charInst ctx nc (toExpr k) reflBoolTrue
  closeGoal <| ncx.applyEqs h

def setDiseqUnsat (c : DiseqCnstr) : RingM Unit := do
  trace_goal[grind.ring.assert.unsat] "{← c.denoteExpr}"
  let ncx ← c.mkNullCertExt
  trace_goal[grind.ring.assert.unsat] "multiplier: {c.d.getMultiplier}, {ncx.d}*({← c.d.p.denoteExpr}), {← (← ncx.toPoly).denoteExpr}"
  let nc := toExpr (ncx.toNullCert)
  let ring ← getRing
  let ctx ← toContextExpr
  let k := c.d.getMultiplier * ncx.d
  let h := match (← nonzeroCharInst?), (← getNoZeroDivInstIfNeeded? k) with
    | some (charInst, char), some nzDivInst =>
      mkApp8 (mkConst ``Grind.CommRing.NullCert.ne_nzdiv_unsatC [ring.u]) ring.type (toExpr char) ring.commRingInst charInst nzDivInst ctx nc (toExpr k)
    | some (charInst, char), none =>
      mkApp6 (mkConst ``Grind.CommRing.NullCert.ne_unsatC [ring.u]) ring.type (toExpr char) ring.commRingInst charInst ctx nc
    | none, some nzDivInst =>
      mkApp6 (mkConst ``Grind.CommRing.NullCert.ne_nzdiv_unsat [ring.u]) ring.type ring.commRingInst nzDivInst ctx nc (toExpr k)
    | none, none =>
      mkApp4 (mkConst ``Grind.CommRing.NullCert.ne_unsat [ring.u]) ring.type ring.commRingInst ctx nc
  let h := mkApp4 h (toExpr c.rlhs) (toExpr c.rrhs) reflBoolTrue (← mkDiseqProof c.lhs c.rhs)
  closeGoal <| ncx.applyEqs h

def propagateEq (a b : Expr) (ra rb : RingExpr) (d : PolyDerivation) : RingM Unit := do
  let ncx ← d.mkNullCertExt
  let nc := toExpr (ncx.toNullCert)
  let ring ← getRing
  let ctx ← toContextExpr
  let k := d.getMultiplier * ncx.d
  let h := match (← nonzeroCharInst?), (← getNoZeroDivInstIfNeeded? k) with
    | some (charInst, char), some nzDivInst =>
      mkApp8 (mkConst ``Grind.CommRing.NullCert.eq_nzdivC [ring.u]) ring.type (toExpr char) ring.commRingInst charInst nzDivInst ctx nc (toExpr k)
    | some (charInst, char), none =>
      mkApp6 (mkConst ``Grind.CommRing.NullCert.eqC [ring.u]) ring.type (toExpr char) ring.commRingInst charInst ctx nc
    | none, some nzDivInst =>
      mkApp6 (mkConst ``Grind.CommRing.NullCert.eq_nzdiv [ring.u]) ring.type ring.commRingInst nzDivInst ctx nc (toExpr k)
    | none, none =>
      mkApp4 (mkConst ``Grind.CommRing.NullCert.eq [ring.u]) ring.type ring.commRingInst ctx nc
  let h := mkApp3 h (toExpr ra) (toExpr rb) reflBoolTrue
  trace_goal[grind.debug.ring.impEq] "{a}, {b}"
  let eq := mkApp3 (mkConst ``Eq [.succ ring.u]) ring.type a b
  pushEq a b <| mkExpectedPropHint (ncx.applyEqs h) eq

end Null

namespace Stepwise
/-!
Alternative proof term construction where we generate a sub-term for each step in
the derivation.
-/

structure ProofM.State where
  cache       : Std.HashMap UInt64 Expr := {}
  polyMap     : Std.HashMap Poly Expr := {}
  monMap      : Std.HashMap Mon Expr := {}
  exprMap     : Std.HashMap RingExpr Expr := {}

structure ProofM.Context where
  ctx : Expr

abbrev ProofM := ReaderT ProofM.Context (StateRefT ProofM.State RingM)

/-- Returns a Lean expression representing the variable context used to construct `CommRing` proof steps. -/
private abbrev getContext : ProofM Expr := do
  return (← read).ctx

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

def mkExprDecl (e : RingExpr) : ProofM Expr := do
  if let some x := (← get).exprMap[e]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with exprMap := s.exprMap.insert e x }
  return x

def mkMonDecl (m : Mon) : ProofM Expr := do
  if let some x := (← get).monMap[m]? then
    return x
  let x := mkFVar (← mkFreshFVarId)
  modify fun s => { s with monMap := s.monMap.insert m x }
  return x

private def mkStepBasicPrefix (declName : Name) : ProofM Expr := do
  let ctx ← getContext
  let ring ← getRing
  return mkApp3 (mkConst declName [ring.u]) ring.type ring.commRingInst ctx

private def mkStepPrefix (declName declNameC : Name) : ProofM Expr := do
  if let some (charInst, char) ← nonzeroCharInst? then
    let ctx ← getContext
    let ring ← getRing
    return mkApp5 (mkConst declNameC [ring.u]) ring.type (toExpr char) ring.commRingInst charInst ctx
  else
    mkStepBasicPrefix declName

open Lean.Grind.CommRing in
partial def _root_.Lean.Meta.Grind.Arith.CommRing.EqCnstr.toExprProof (c : EqCnstr) : ProofM Expr := caching c do
  match c.h with
  | .core a b lhs rhs =>
    let h ← mkStepPrefix ``Stepwise.core ``Stepwise.coreC
    return mkApp5 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl c.p) reflBoolTrue (← mkEqProof a b)
  | .superpose k₁ m₁ c₁ k₂ m₂ c₂ =>
    let h ← mkStepPrefix ``Stepwise.superpose ``Stepwise.superposeC
    return mkApp10 h
      (toExpr k₁) (← mkMonDecl m₁) (← mkPolyDecl c₁.p)
      (toExpr k₂) (← mkMonDecl m₂) (← mkPolyDecl c₂.p)
      (← mkPolyDecl c.p) reflBoolTrue (← toExprProof c₁) (← toExprProof c₂)
  | .simp k₁ c₁ k₂ m₂ c₂ =>
    let h ← mkStepPrefix ``Stepwise.simp ``Stepwise.simpC
    return mkApp9 h
      (toExpr k₁) (← mkPolyDecl c₁.p)
      (toExpr k₂) (← mkMonDecl m₂) (← mkPolyDecl c₂.p)
      (← mkPolyDecl c.p) reflBoolTrue (← toExprProof c₁) (← toExprProof c₂)
  | .mul k c₁ =>
    let h ← mkStepPrefix ``Stepwise.mul ``Stepwise.mulC
    return mkApp5 h (← mkPolyDecl c₁.p) (toExpr k) (← mkPolyDecl c.p) reflBoolTrue (← toExprProof c₁)
  | .div k c₁ =>
    let h ← mkStepPrefix ``Stepwise.div ``Stepwise.divC
    let some nzInst ← noZeroDivisorsInst?
      | throwNoNatZeroDivisors
    return mkApp6 h nzInst (← mkPolyDecl c₁.p) (toExpr k) (← mkPolyDecl c.p) reflBoolTrue (← toExprProof c₁)

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
      reflBoolTrue h₁ h₂
    return (k₁*k, p₀, h)

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
  return mkApp6 h (← mkExprDecl lhs) (← mkExprDecl rhs) (← mkPolyDecl p₀) (← mkPolyDecl d.p) reflBoolTrue h₁

private abbrev withProofContext (x : ProofM Expr) : RingM Expr := do
  let ring ← getRing
  withLetDecl `ctx (mkApp (mkConst ``RArray [ring.u]) ring.type) (← toContextExpr) fun ctx =>
  go { ctx } |>.run' {}
where
  go : ProofM Expr := do
    let h ← x
    let h ← mkLetOfMap (← get).polyMap h `p (mkConst ``Grind.CommRing.Poly) toExpr
    let h ← mkLetOfMap (← get).monMap h `m (mkConst ``Grind.CommRing.Mon) toExpr
    let h ← mkLetOfMap (← get).exprMap h `e (mkConst ``Grind.CommRing.Expr) toExpr
    mkLetFVars #[(← getContext)] h

open Lean.Grind.CommRing in
def setEqUnsat (c : EqCnstr) : RingM Unit := do
  let h ← withProofContext do
    let ring ← getRing
    if let some (charInst, char) := ring.charInst? then
      let mut h ← mkStepPrefix ``Stepwise.unsat_eq ``Stepwise.unsat_eqC
      if char == 0 then
        h := mkApp h charInst
      let k ← getPolyConst c.p
      return mkApp4 h (← mkPolyDecl c.p) (toExpr k) reflBoolTrue (← c.toExprProof)
    else if let some fieldInst := ring.fieldInst? then
      return mkApp6 (mkConst ``Grind.CommRing.one_eq_zero_unsat [ring.u]) ring.type fieldInst (← getContext)
        (← mkPolyDecl c.p) reflBoolTrue (← c.toExprProof)
    else
      throwError "`grind ring` internal error, unexpected unsat eq proof {← c.denoteExpr}"
  closeGoal h

def setDiseqUnsat (c : DiseqCnstr) : RingM Unit := do
  let heq ← withProofContext do
    mkImpEqExprProof c.rlhs c.rrhs c.d
  closeGoal <| mkApp (← mkDiseqProof c.lhs c.rhs) heq

def propagateEq (a b : Expr) (ra rb : RingExpr) (d : PolyDerivation) : RingM Unit := do
  let heq ← withProofContext do
    mkImpEqExprProof ra rb d
  let ring ← getRing
  let eq := mkApp3 (mkConst ``Eq [.succ ring.u]) ring.type a b
  pushEq a b <| mkExpectedPropHint heq eq

end Stepwise

def EqCnstr.setUnsat (c : EqCnstr) : RingM Unit := do
  if (← getConfig).ringNull then
    Null.setEqUnsat c
  else
    Stepwise.setEqUnsat c

def DiseqCnstr.setUnsat (c : DiseqCnstr) : RingM Unit := do
  if (← getConfig).ringNull then
    Null.setDiseqUnsat c
  else
    Stepwise.setDiseqUnsat c

def propagateEq (a b : Expr) (ra rb : RingExpr) (d : PolyDerivation) : RingM Unit := do
  if (← getConfig).ringNull then
    Null.propagateEq a b ra rb d
  else
    Stepwise.propagateEq a b ra rb d

end Lean.Meta.Grind.Arith.CommRing
