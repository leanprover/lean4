/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Arith.Ring.DenoteExpr
public import Lean.Meta.Sym.Arith.Ring.Detect
public import Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
import Lean.Meta.Sym.LitValues
import Lean.Meta.Sym.InferType
public import Lean.Meta.SynthInstance
import Lean.Data.RArray
import Init.Grind.Ring
public section
namespace Lean.Meta.Sym.Simp

open Arith.Ring

/-!
# Arithmetic Normalizer for Sym.simp

A simproc that normalizes ring expressions to polynomial normal form.
Given an expression like `(a + b) * (a - b)`, it normalizes to `a*a + (-1)*b*b`
(i.e., the polynomial representation), and produces an equality proof using
`Grind.CommRing.Expr.denote_toPoly`.
-/

/-- Monad for ring operations within the normalizer. Wraps `SimpM` with a current ring id. -/
structure ArithRingM.Context where
  ringId : Nat

abbrev ArithRingM := ReaderT ArithRingM.Context SimpM

instance : MonadCanon ArithRingM where
  canonExpr e := shareCommonInc e
  synthInstance? e := Meta.synthInstance? e

builtin_initialize arithExt : SymExtension Arith.Ring.State ← registerSymExtension

def ArithRingM.getCommRing : ArithRingM CommRing := do
  let s ← arithExt.getState
  let ringId := (← read).ringId
  if h : ringId < s.rings.size then
    return s.rings[ringId]
  else
    throwError "arith normalizer: invalid ringId"

def ArithRingM.modifyCommRing (f : CommRing → CommRing) : ArithRingM Unit := do
  let ringId := (← read).ringId
  arithExt.modifyState fun s => { s with rings := s.rings.modify ringId f }
  -- Write-through: update shared cache so grind benefits from lazily-computed operations
  let ring ← ArithRingM.getCommRing
  Arith.Ring.updateSharedRing ring

instance : MonadRing ArithRingM where
  getRing := return (← ArithRingM.getCommRing).toRing
  modifyRing f := ArithRingM.modifyCommRing fun s => { s with toRing := f s.toRing }

/-- Detect whether `type` has a `Grind.CommRing` instance. Returns the local ring id if found. -/
private def getCommRingId? (type : Expr) : SimpM (Option Nat) := do
  let s ← arithExt.getState
  if let some id? := s.typeIdOf.find? { expr := type } then
    return id?
  let some tmpl ← Arith.Ring.detectCommRing? type | do
    arithExt.modifyState fun st => { st with typeIdOf := st.typeIdOf.insert { expr := type } none }
    return none
  let id := s.rings.size
  let ring := { tmpl with toRing.id := id }
  arithExt.modifyState fun st => { st with
    rings := st.rings.push ring
    typeIdOf := st.typeIdOf.insert { expr := type } (some id)
  }
  return some id

/-- Check if an expression is an instance of the expected one by pointer equality. -/
private def isExpectedInst (expected inst : Expr) : Bool :=
  isSameExpr expected.appArg! inst

/--
Reify a Lean expression into a `RingExpr`.
Returns `none` if the expression is not a ring term.
-/
private partial def reify? (e : Expr) : ArithRingM (Option RingExpr) := do
  let mkVar (e : Expr) : ArithRingM Grind.CommRing.Var := do
    let ring ← getRing
    if let some var := ring.varMap.find? { expr := e } then
      return var
    let var : Grind.CommRing.Var := ring.vars.size
    modifyRing fun s => { s with
      vars   := s.vars.push e
      varMap := s.varMap.insert { expr := e } var
    }
    return var
  let toVar (e : Expr) : ArithRingM RingExpr := do
    return .var (← mkVar e)
  let rec go (e : Expr) : ArithRingM RingExpr := do
    match_expr e with
    | HAdd.hAdd _ _ _ i a b =>
      if isExpectedInst (← getAddFn) i then return .add (← go a) (← go b) else toVar e
    | HMul.hMul _ _ _ i a b =>
      if isExpectedInst (← getMulFn) i then return .mul (← go a) (← go b) else toVar e
    | HSub.hSub _ _ _ i a b =>
      if isExpectedInst (← getSubFn) i then return .sub (← go a) (← go b) else toVar e
    | HPow.hPow _ _ _ i a b =>
      let some k := getNatValue? b | toVar e
      if isExpectedInst (← getPowFn) i then return .pow (← go a) k else toVar e
    | Neg.neg _ i a =>
      if isExpectedInst (← getNegFn) i then return .neg (← go a) else toVar e
    | IntCast.intCast _ i a =>
      if isExpectedInst (← getIntCastFn) i then
        let some k := getIntValue? a | toVar e
        return .intCast k
      else
        toVar e
    | NatCast.natCast _ i a =>
      if isExpectedInst (← getNatCastFn) i then
        let some k := getNatValue? a | toVar e
        return .natCast k
      else
        toVar e
    | OfNat.ofNat _ n _ =>
      let .lit (.natVal k) := n | toVar e
      return .num k
    | _ => toVar e
  -- At top level, only proceed if e is an arithmetic operation
  match_expr e with
  | HAdd.hAdd _ _ _ i a b =>
    if isExpectedInst (← getAddFn) i then return some (.add (← go a) (← go b)) else return none
  | HMul.hMul _ _ _ i a b =>
    if isExpectedInst (← getMulFn) i then return some (.mul (← go a) (← go b)) else return none
  | HSub.hSub _ _ _ i a b =>
    if isExpectedInst (← getSubFn) i then return some (.sub (← go a) (← go b)) else return none
  | HPow.hPow _ _ _ i a b =>
    let some k := getNatValue? b | return none
    if isExpectedInst (← getPowFn) i then return some (.pow (← go a) k) else return none
  | Neg.neg _ i a =>
    if isExpectedInst (← getNegFn) i then return some (.neg (← go a)) else return none
  | _ => return none

/--
Build a `Grind.CommRing.Context α` expression (an `RArray α`) from the variable array.
-/
private def toContextExpr : ArithRingM Expr := do
  let ring ← getRing
  let vars := ring.vars.toArray
  if h : 0 < vars.size then
    RArray.toExpr ring.type id (RArray.ofFn (vars[·]) h)
  else
    RArray.toExpr ring.type id (RArray.leaf (mkApp (← getNatCastFn) (toExpr 0)))

/--
The core arithmetic normalization logic.
Given a ring expression, normalize it to polynomial form and produce a proof.
-/
private def normalizeRingExpr (re : RingExpr) : ArithRingM (Option Result) := do
  let ring ← getRing
  let commRing ← ArithRingM.getCommRing
  -- Normalize to polynomial
  let p := match ring.charInst? with
    | some (_, c) => if c != 0 then re.toPolyC c else re.toPoly
    | none => re.toPoly
  -- Build the denotation of the polynomial as a Lean expression
  let e' ← denotePoly p
  let e' ← shareCommonInc e'
  -- Build the context (RArray of variable denotations)
  let ctx ← toContextExpr
  let ctx ← shareCommonInc ctx
  -- Build the reified expression as a Lean Expr
  let reExpr := toExpr re
  -- Build proof: denote_toPoly ctx re : re.toPoly.denote ctx = re.denote ctx
  -- We need: e = e', i.e., re.denote ctx = re.toPoly.denote ctx
  -- denote_toPoly gives: re.toPoly.denote ctx = re.denote ctx, i.e., e' = e
  -- So we use Eq.symm
  let u := commRing.u
  let ringInst := mkApp2 (mkConst ``Grind.CommRing.toRing [u]) ring.type commRing.commRingInst
  -- Build `re.denote ctx` as a Lean expression (for Eq.symm argument)
  let eOrig := mkApp4 (mkConst ``Grind.CommRing.Expr.denote [u]) ring.type ringInst ctx reExpr
  let proof ← match ring.charInst? with
    | some (charInst, c) =>
      if c != 0 then
        -- denote_toPolyC : ∀ {α c} [CommRing α] [IsCharP α c] (ctx) (e), (e.toPolyC c).denote ctx = e.denote ctx
        let proofFwd := mkApp6 (mkConst ``Grind.CommRing.Expr.denote_toPolyC [u])
          ring.type (toExpr c) commRing.commRingInst charInst ctx reExpr
        pure <| mkApp4 (mkConst ``Eq.symm [u.succ]) ring.type e' eOrig proofFwd
      else
        let proofFwd := mkApp4 (mkConst ``Grind.CommRing.Expr.denote_toPoly [u])
          ring.type commRing.commRingInst ctx reExpr
        pure <| mkApp4 (mkConst ``Eq.symm [u.succ]) ring.type e' eOrig proofFwd
    | none =>
      let proofFwd := mkApp4 (mkConst ``Grind.CommRing.Expr.denote_toPoly [u])
        ring.type commRing.commRingInst ctx reExpr
      pure <| mkApp4 (mkConst ``Eq.symm [u.succ]) ring.type e' eOrig proofFwd
  return some (.step e' proof)

/--
Create an arithmetic normalizer simproc.
The returned simproc normalizes ring expressions to polynomial normal form.
-/
def mkArithNormSimproc : SymM Simproc := do
  return fun e => do
    -- Quick check: is this an arithmetic operation?
    unless e.isApp do return .rfl
    let fn := e.getAppFn
    unless fn.isConst do return .rfl
    let name := fn.constName!
    unless name == ``HAdd.hAdd || name == ``HMul.hMul || name == ``HSub.hSub
        || name == ``HPow.hPow || name == ``Neg.neg do
      return .rfl
    -- Infer the type of the expression
    let type ← Sym.inferType e
    let type ← shareCommonInc type
    -- Try to find a CommRing instance for this type
    let some ringId ← getCommRingId? type | return .rfl
    -- Run normalization in the ring context
    let ctx : ArithRingM.Context := { ringId }
    let r ← (do
      let some re ← reify? e | return Result.rfl
      let some result ← normalizeRingExpr re | return Result.rfl
      return result : ArithRingM Result) ctx
    return r

end Lean.Meta.Sym.Simp
