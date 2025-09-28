/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Init.Data.Int.OfNat
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat
import Lean.Meta.Tactic.Grind.Order.StructId
import Lean.Meta.Tactic.Grind.Order.Util
import Lean.Meta.Tactic.Grind.Order.Assert
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
  if let some parent := parent? then
    getType? parent |>.isSome
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

def propEq := mkApp (mkConst ``Eq [1]) (mkSort 0)

/--
Given a proof `h` that `e = rel lhs rhs`, returns `(e', h')` where
`e'` is `rel lhs rhs`, and `h'` is `h` with the expected proposition hint around it.
-/
def mkExpectedHint (s : Struct) (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) (h : Expr) : Expr × Expr :=
  let rel := match kind with
    | .le => s.leFn
    | .lt => s.ltFn?.get!
    | .eq => mkApp (mkConst ``Eq [mkLevelSucc s.u]) s.type
  let e' := mkApp2 rel lhs rhs
  let prop :=  mkApp2 propEq e e'
  let h' := mkExpectedPropHint h prop
  (e', h')

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
  | .eq => mkEqNorm0 s ringInst lhs rhs

/--
Returns `rel lhs (rhs + 0)`
-/
def mkDenote0 [MonadLiftT MetaM m] [MonadError m] [Monad m] [MonadCanon m] [MonadRing m]
    (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : m Expr := do
  let rel := match kind with
    | .le => s.leFn
    | .lt => s.ltFn?.get!
    | .eq => mkApp (mkConst ``Eq [mkLevelSucc s.u]) s.type
  let rhs' := mkApp2 (← getAddFn) rhs (mkApp (← getIntCastFn) (mkIntLit 0))
  return mkApp2 rel lhs rhs'

def mkCommRingCnstr? (e : Expr) (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : RingM (Option (Cnstr Expr)) := do
  if !isArithTerm lhs && !isArithTerm rhs then
    let e ← mkDenote0 s kind lhs rhs
    return some { u := lhs, v := rhs, k := 0, e, kind, h? := some (mkCnstrNorm0 s (← getRing).ringInst kind lhs rhs)  }
  let some lhs ← reify? lhs (skipVar := false) | return none
  let some rhs ← reify? rhs (skipVar := false) | return none
  let p ← lhs.sub rhs |>.toPolyM
  let (lhs', rhs', k) := split p
  let lhs' := lhs'.toExpr
  let rhs' := rhs'.toExpr
  let u ← shareCommon (← lhs'.denoteExpr)
  let v ← shareCommon (← rhs'.denoteExpr)
  let rhs' : RingExpr := .add rhs' (.intCast k)
  let h ← match kind with
    | .le => mkLeIffProof s.leInst s.ltInst?.get! s.isPreorderInst s.orderedRingInst?.get! lhs rhs lhs' rhs'
    | .lt => mkLtIffProof s.leInst s.ltInst?.get! s.lawfulOrderLTInst?.get! s.isPreorderInst s.orderedRingInst?.get! lhs rhs lhs' rhs'
    | .eq => mkEqIffProof lhs rhs lhs' rhs'
  let (e', h') := mkExpectedHint s e kind u (← rhs'.denoteExpr) h
  return some {
    kind, u, v, k, e := e', h? := some h'
  }

def mkNonCommRingCnstr? (e : Expr) (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : NonCommRingM (Option (Cnstr Expr)) := do
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
    | .eq => mkNonCommEqIffProof lhs rhs lhs' rhs'
  let (e', h') := mkExpectedHint s e kind u (← rhs'.denoteExpr) h
  return some {
    kind, u, v, k, e := e', h? := some h'
  }

def mkCnstr? (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) : OrderM (Option (Cnstr Expr)) := do
  let s ← getStruct
  if let some ringId := s.ringId? then
    if s.isCommRing then
      RingM.run ringId <| mkCommRingCnstr? e s kind lhs rhs
    else
      NonCommRingM.run ringId <| mkNonCommRingCnstr? e s kind lhs rhs
  else
    return some { kind, u := lhs, v := rhs, e }

def setStructId (e : Expr) : OrderM Unit := do
  let structId ← getStructId
  modify' fun s => { s with
    exprToStructId := s.exprToStructId.insert { expr := e } structId
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
  return nodeId

def internalizeCnstr (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) : OrderM Unit := do
  let some c ← mkCnstr? e kind lhs rhs | return ()
  trace[grind.order.internalize] "{c.u}, {c.v}, {c.k}"
  if grind.debug.get (← getOptions) then
    if let some h := c.h? then check h
  let u ← mkNode c.u
  let v ← mkNode c.v
  let c := { c with u, v }
  if let some k' := c.getWeight? then
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

open Arith.Cutsat in
def adaptNat (e : Expr) : GoalM Expr := do
  let (eNew, h) ← match_expr e with
    | LE.le _ _ lhs rhs =>
      let (lhs', h₁) ← natToInt lhs
      let (rhs', h₂) ← natToInt rhs
      let eNew := mkIntLE lhs' rhs'
      let h := mkApp6 (mkConst ``Nat.ToInt.le_eq) lhs rhs lhs' rhs' h₁ h₂
      pure (eNew, h)
    | LT.lt _ _ lhs rhs =>
      let (lhs', h₁) ← natToInt lhs
      let (rhs', h₂) ← natToInt rhs
      let eNew := mkIntLT lhs' rhs'
      let h := mkApp6 (mkConst ``Nat.ToInt.lt_eq) lhs rhs lhs' rhs' h₁ h₂
      pure (eNew, h)
    | Eq _ lhs rhs =>
      let (lhs', h₁) ← natToInt lhs
      let (rhs', h₂) ← natToInt rhs
      let eNew := mkIntEq lhs' rhs'
      let h := mkApp6 (mkConst ``Nat.ToInt.eq_eq) lhs rhs lhs' rhs' h₁ h₂
      pure (eNew, h)
    | _ => return e
  modify' fun s => { s with
    cnstrsMap    := s.cnstrsMap.insert { expr := e } (eNew, h)
    cnstrsMapInv := s.cnstrsMapInv.insert { expr := eNew } (e, h)
  }
  return eNew

def adapt (α : Expr) (e : Expr) : GoalM (Expr × Expr) := do
  -- **Note**: We currently only adapt `Nat` expressions
  if α == Nat.mkType then
    let eNew ← adaptNat e
    return ((← getIntExpr), eNew)
  else
    return (α, e)

def alreadyInternalized (e : Expr) : OrderM Bool := do
  let s ← getStruct
  return s.cnstrs.contains { expr := e } || s.nodeMap.contains { expr := e }

public def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).order do return ()
  let some α := getType? e | return ()
  let (α, e) ← adapt α e
  if isForbiddenParent parent? then return ()
  if let some structId ← getStructId? α then OrderM.run structId do
    if (← alreadyInternalized e) then return ()
    match_expr e with
    | LE.le _ _ lhs rhs => internalizeCnstr e .le lhs rhs
    | LT.lt _ _ lhs rhs => if (← hasLt) then internalizeCnstr e .lt lhs rhs
    | Eq _ lhs rhs => internalizeCnstr e .eq lhs rhs
    | _ =>
      -- TODO
      return ()

end Lean.Meta.Grind.Order
