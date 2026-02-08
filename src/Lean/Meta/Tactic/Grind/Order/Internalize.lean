/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Init.Data.Int.OfNat
import Init.Grind.Module.Envelope
import Init.Grind.Order
import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Order.StructId
import Lean.Meta.Tactic.Grind.Order.Util
import Lean.Meta.Tactic.Grind.Order.Assert
import Lean.Meta.Tactic.Grind.Order.Proof
namespace Lean.Meta.Grind.Order

open Arith CommRing

def getType? (e : Expr) : Option Expr :=
  match_expr e with
  | Eq α lhs rhs =>
    /-
    **Note**: We only try internalize equalities if `lhs` or `rhs` arithmetic terms that may
    need to be internalized. If they are not, normalization is not needed. Moreover, this is
    an optimization for avoiding trying to infer order instances for "hopeless" types such as
    `Bool`.
    -/
    if isArithTerm lhs || isArithTerm rhs then
      some α
    else
      none
  | LE.le α _ _ _ => some α
  | LT.lt α _ _ _ => some α
  | HAdd.hAdd α _ _ _ _ _ => some α
  | HSub.hSub α _ _ _ _ _ => some α
  | OfNat.ofNat α _ _ => some α
  | _ => none

def isForbiddenParent (parent? : Option Expr) : Bool :=
  if isIntModuleVirtualParent parent? then
    /-
    **Note**: `linarith` uses a virtual parent to mark auxiliary declarations used to encode
    terms into an `IntModule`.
    -/
    true
  else if let some parent := parent? then
    if parent.isEq then
      false
    else
      (getType? parent |>.isSome)
      ||
      /-
      **Note**: We currently ignore `•`. We may reconsider it in the future.
      -/
      match_expr parent with
      | HSMul.hSMul _ _ _ _ _ _ => true
      | Nat.cast _ _ _ => true
      | NatCast.natCast _ _ _ => true
      | Grind.IntModule.OfNatModule.toQ _ _ _ => true
      | _ => false
  else
    false

def split (p : Poly) : Poly × Poly × Int :=
  match p with
  | .num k => (.num 0, .num 0, -k)
  | .add k m p =>
    let (lhs, rhs, c) := split p
    if k < 0 then
      (lhs, .add (-k) m rhs, c)
    else
      (.add k m lhs, rhs, c)

def mkRel (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : Expr :=
  let rel := match kind with
    | .le => s.leFn
    | .lt => s.ltFn?.get!
  mkApp2 rel lhs rhs

def mkLeNorm0 (s : Struct) (ringInst : Expr) (lhs rhs : Expr) : Expr :=
  mkApp5 (mkConst ``Grind.CommRing.le_norm0 [s.u]) s.type ringInst s.leInst lhs rhs

def mkLtNorm0 (s : Struct) (ringInst : Expr) (lhs rhs : Expr) : Expr :=
  mkApp5 (mkConst ``Grind.CommRing.lt_norm0 [s.u]) s.type ringInst s.ltInst?.get! lhs rhs

def mkEqNorm0 (s : Struct) (ringInst : Expr) (lhs rhs : Expr) : Expr :=
  mkApp4 (mkConst ``Grind.CommRing.eq_norm0 [s.u]) s.type ringInst lhs rhs

def mkCnstrNorm0 (s : Struct) (ringInst : Expr) (kind : CnstrKind) (lhs rhs : Expr) : Expr :=
  match kind with
  | .le => mkLeNorm0 s ringInst lhs rhs
  | .lt => mkLtNorm0 s ringInst lhs rhs

/--
Returns `rel lhs (rhs + 0)`
-/
def mkDenote0 [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m] [MonadRing m]
    (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : m Expr := do
  let rhs' := mkApp2 (← getAddFn) rhs (mkApp (← getIntCastFn) (mkIntLit 0))
  return mkRel s kind lhs rhs'

def mkCommRingCnstr? (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : RingM (Option (Cnstr Expr)) := do
  if !isArithTerm lhs && !isArithTerm rhs then
    let e ← mkDenote0 s kind lhs rhs
    return some { u := lhs, v := rhs, k := 0, e, kind, h? := some (mkCnstrNorm0 s (← getRing).ringInst kind lhs rhs)  }
  let some lhs ← reify? lhs (skipVar := false) | return none
  let some rhs ← reify? rhs (skipVar := false) | return none
  let some p ← lhs.sub rhs |>.toPolyM? | return none
  let (lhs', rhs', k) := split p
  let lhs' := lhs'.toExpr
  let rhs' := rhs'.toExpr
  let u ← shareCommon (← lhs'.denoteExpr)
  let v ← shareCommon (← rhs'.denoteExpr)
  let rhs' : RingExpr := .add rhs' (.intCast k)
  let h ← match kind with
    | .le => mkLeIffProof s.leInst s.ltInst?.get! s.isPreorderInst s.orderedRingInst?.get! lhs rhs lhs' rhs'
    | .lt => mkLtIffProof s.leInst s.ltInst?.get! s.lawfulOrderLTInst?.get! s.isPreorderInst s.orderedRingInst?.get! lhs rhs lhs' rhs'
  let e' := mkRel s kind u (← rhs'.denoteExpr)
  return some {
    kind, u, v, k, e := e', h? := some h
  }

def mkNonCommRingCnstr? (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : NonCommRingM (Option (Cnstr Expr)) := do
  if !isArithTerm lhs && !isArithTerm rhs then
    let e ← mkDenote0 s kind lhs rhs
    return some { u := lhs, v := rhs, k := 0, e, kind, h? := some (mkCnstrNorm0 s (← getRing).ringInst kind lhs rhs)  }
  let some lhs ← ncreify? lhs (skipVar := false) | return none
  let some rhs ← ncreify? rhs (skipVar := false) | return none
  -- **TODO**: We need a `toPolyM_nc` similar `toPolyM`
  let p := lhs.sub rhs |>.toPoly_nc
  let (lhs', rhs', k) := split p
  let lhs' := lhs'.toExpr
  let rhs' := rhs'.toExpr
  let u ← shareCommon (← lhs'.denoteExpr)
  let v ← shareCommon (← rhs'.denoteExpr)
  let rhs' : RingExpr := .add rhs' (.intCast k)
  let h ← match kind with
    | .le => mkNonCommLeIffProof s.leInst s.ltInst?.get! s.isPreorderInst s.orderedRingInst?.get! lhs rhs lhs' rhs'
    | .lt => mkNonCommLtIffProof s.leInst s.ltInst?.get! s.lawfulOrderLTInst?.get! s.isPreorderInst s.orderedRingInst?.get! lhs rhs lhs' rhs'
  let e' := mkRel s kind u (← rhs'.denoteExpr)
  return some {
    kind, u, v, k, e := e', h? := some h
  }

def mkCnstr? (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) : OrderM (Option (Cnstr Expr)) := do
  let s ← getStruct
  if let some ringId := s.ringId? then
    if s.isCommRing then
      RingM.run ringId <| mkCommRingCnstr? s kind lhs rhs
    else
      NonCommRingM.run ringId <| mkNonCommRingCnstr? s kind lhs rhs
  else
    return some { kind, u := lhs, v := rhs, e }

def setStructId (e : Expr) : OrderM Unit := do
  let structId ← getStructId
  modify' fun s => { s with
    exprToStructId := s.exprToStructId.insert { expr := e } structId
  }

def updateTermMap (e eNew h : Expr) : GoalM Unit := do
  modify' fun s => { s with
    termMap    := s.termMap.insert { expr := e } (eNew, h)
    termMapInv := s.termMapInv.insert { expr := eNew } (e, h)
  }

def mkNode (e : Expr) : OrderM NodeId := do
  if let some nodeId := (← getStruct).nodeMap.find? { expr := e } then
    return nodeId
  let nodeId : NodeId := (← getStruct).nodes.size
  trace[grind.order.internalize.term] "{e} ↦ #{nodeId}"
  modifyStruct fun s => { s with
    nodes   := s.nodes.push e
    nodeMap := s.nodeMap.insert { expr := e } nodeId
    sources := s.sources.push {}
    targets := s.targets.push {}
    proofs  := s.proofs.push {}
  }
  setStructId e
  /-
  **Note**: not all node expressions have been internalized because this solver
  creates auxiliary terms.
  -/
  if (← alreadyInternalized e) then
    orderExt.markTerm e
  if let some e' ← getOriginal? e then
    orderExt.markTerm e'
  return nodeId
where
  getOriginal? (e : Expr) : GoalM (Option Expr) := do
    if let some (e', _) := (← get').termMapInv.find? { expr := e } then
      return some e'
    let_expr NatCast.natCast _ _ a := e | return none
    if (← alreadyInternalized a) then
      updateTermMap a e (← mkEqRefl e)
      return some a
    else
      return none

def internalizeCnstr (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) : OrderM Unit := do
  let some c ← mkCnstr? e kind lhs rhs | return ()
  trace[grind.order.internalize] "{c.u}, {c.v}, {c.k}"
  if (← isDebugEnabled) then
    if let some h := c.h? then check h
  let u ← mkNode c.u
  let v ← mkNode c.v
  let c := { c with u, v }
  let k' := c.getWeight
  if u == v then
    if k'.isNeg then
      propagateSelfEqFalse c e
    else
      propagateSelfEqTrue c e
    return ()
  if let some k ← getDist? u v then
    if k ≤ k' then
      propagateEqTrue c e u v k k'
      return ()
  if let some k ← getDist? v u then
    if (k + k').isNeg then
      propagateEqFalse c e v u k k'
      return ()
  setStructId e
  modifyStruct fun s => { s with
    cnstrs   := s.cnstrs.insert { expr := e } c
    cnstrsOf :=
      let cs := if let some cs := s.cnstrsOf.find? (u, v) then (c, e) :: cs else [(c, e)]
      s.cnstrsOf.insert (u, v) cs
  }

/--
Normalization result. A nested term `e` is normalized as `a + k` and
`h` is a proof for `e = a + k`
-/
structure OffsetTermResult where
  a : Expr
  k : Int
  h : Expr

def toOffsetTermCommRing? (e : Expr) : RingM (Option OffsetTermResult) := do
  let some e ← reify? e (skipVar := false) | return none
  let some p ← e.toPolyM? | return none
  let k := p.getConst
  let p := p.addConst (-k)
  let a ← shareCommon (← p.denoteExpr)
  let h ← mkTermEqProof e (.add (p.toExpr) (.intCast k))
  return some { a, k, h }

def toOffsetTermNonCommRing? (e : Expr) : NonCommRingM (Option OffsetTermResult) := do
  let some e ← ncreify? e (skipVar := false) | return none
  let p := e.toPoly_nc
  let k := p.getConst
  let p := p.addConst (-k)
  let a ← shareCommon (← p.denoteExpr)
  let h ← mkNonCommTermEqProof e (.add (p.toExpr) (.intCast k))
  return some { a, k, h }

def toOffsetTerm? (e : Expr) : OrderM (Option OffsetTermResult) := do
  let s ← getStruct
  /-
  **Note**: If it is not a partial order, then it is not worth internalizing term
  since we will not be able to propagate implied equalities back to core.
  -/
  unless s.isPartialInst?.isSome do return none
  let some ringId := s.ringId? | return none
  if s.isCommRing then
    RingM.run ringId <| toOffsetTermCommRing? e
  else
    NonCommRingM.run ringId <| toOffsetTermNonCommRing? e

def internalizeTerm (e : Expr) : OrderM Unit := do
  let some r ← toOffsetTerm? e | return ()
  if e == r.a && r.k == 0 then return ()
  let x ← mkNode e
  let y ← mkNode r.a
  let h₁ ← mkOrdRingPrefix ``Grind.Order.le_of_offset_eq_1_k
  let h₁ := mkApp4 h₁ e r.a (toExpr r.k) r.h
  addEdge x y { k := r.k } h₁
  let h₂ ← mkOrdRingPrefix ``Grind.Order.le_of_offset_eq_2_k
  let h₂ := mkApp4 h₂ e r.a (toExpr r.k) r.h
  addEdge y x { k := -r.k } h₂

open Arith.Cutsat in
def adaptNat (e : Expr) : GoalM Expr := do
  if let some (eNew, _) := (← get').termMap.find? { expr := e } then
    return eNew
  else match_expr e with
    | LE.le _ _ lhs rhs => adaptCnstr lhs rhs (isLT := false)
    | LT.lt _ _ lhs rhs => adaptCnstr lhs rhs (isLT := true)
    | HAdd.hAdd _ _ _ _ _ _ => adaptTerm
    | HSub.hSub _ _ _ _ _ _ => adaptTerm
    | OfNat.ofNat _ _ _ => adaptTerm
    | _ => return e
where
  adaptCnstr (lhs rhs : Expr) (isLT : Bool) : GoalM Expr := do
    let (lhs', h₁) ← natToInt lhs
    let (rhs', h₂) ← natToInt rhs
    let eNew := if isLT then mkIntLT lhs' rhs' else mkIntLE lhs' rhs'
    let h := mkApp6
        (mkConst (if isLT then ``Nat.ToInt.lt_eq else ``Nat.ToInt.le_eq))
        lhs rhs lhs' rhs' h₁ h₂
    updateTermMap e eNew h
    return eNew

  adaptTerm : GoalM Expr := do
    let (eNew, h) ← natToInt e
    updateTermMap e eNew h
    return eNew

def adapt (α : Expr) (e : Expr) : GoalM (Expr × Expr) := do
  -- **Note**: We currently only adapt `Nat` expressions
  if α == Nat.mkType then
    let eNew ← adaptNat e
    return ((← getIntExpr), eNew)
  else
    return (α, e)

def alreadyInternalizedHere (e : Expr) : OrderM Bool := do
  let s ← getStruct
  return s.cnstrs.contains { expr := e } || s.nodeMap.contains { expr := e }

public def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).order do return ()
  let some α := getType? e | return ()
  let (α, e) ← adapt α e
  if isForbiddenParent parent? then return ()
  if let some structId ← getStructId? α then OrderM.run structId do
    if (← alreadyInternalizedHere e) then return ()
    match_expr e with
    | LE.le _ _ lhs rhs => internalizeCnstr e .le lhs rhs
    | LT.lt _ _ lhs rhs => if (← hasLt) then internalizeCnstr e .lt lhs rhs
    | HAdd.hAdd _ _ _ _ _ _ => internalizeTerm e
    | HSub.hSub _ _ _ _ _ _ => internalizeTerm e
    | OfNat.ofNat _ _ _ => internalizeTerm e
    | _ => return ()

end Lean.Meta.Grind.Order
