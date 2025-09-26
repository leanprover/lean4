/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Order.OrderM
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
import Lean.Meta.Tactic.Grind.Arith.CommRing.Poly
import Lean.Meta.Tactic.Grind.Arith.CommRing.SafePoly
import Lean.Meta.Tactic.Grind.Arith.CommRing.Reify
import Lean.Meta.Tactic.Grind.Arith.CommRing.Functions
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.CommRing.Proof
import Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize
import Lean.Meta.Tactic.Grind.Order.StructId
namespace Lean.Meta.Grind.Order

def getType? (e : Expr) : Option Expr :=
  match_expr e with
  | Eq α _ _ => some α
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

open Arith CommRing

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
Given a proof `h` that `e ↔ rel lhs rhs`, add expected proposition hint around `h`.
The relation `rel` is inferred from `kind`.
-/
def mkExpectedHint (s : Struct) (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) (h : Expr) : Expr :=
  let rel := match kind with
    | .le => s.leFn
    | .lt => s.ltFn?.get!
    | .eq => mkApp (mkConst ``Eq [mkLevelSucc s.u]) s.type
  let e' := mkApp2 rel lhs rhs
  let prop :=  mkApp2 propEq e e'
  mkExpectedPropHint h prop

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

def mkCommRingCnstr? (e : Expr) (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : RingM (Option (Cnstr Expr)) := do
  if !isArithTerm lhs && !isArithTerm rhs then
    return some { u := lhs, v := rhs, k := 0, kind, h? := some (mkCnstrNorm0 s (← getRing).ringInst kind lhs rhs)  }
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
  let h := mkExpectedHint s e kind u (← rhs'.denoteExpr) h
  return some {
    kind, u, v, k, h? := some h
  }

def mkNonCommRingCnstr? (e : Expr) (s : Struct) (kind : CnstrKind) (lhs rhs : Expr) : NonCommRingM (Option (Cnstr Expr)) := do
  if !isArithTerm lhs && !isArithTerm rhs then
    return some { u := lhs, v := rhs, k := 0, kind, h? := some (mkCnstrNorm0 s (← getRing).ringInst kind lhs rhs)  }
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
  let h := mkExpectedHint s e kind u (← rhs'.denoteExpr) h
  return some {
    kind, u, v, k, h? := some h
  }

def mkCnstr? (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) : OrderM (Option (Cnstr Expr)) := do
  let s ← getStruct
  if let some ringId := s.ringId? then
    if s.isCommRing then
      RingM.run ringId <| mkCommRingCnstr? e s kind lhs rhs
    else
      NonCommRingM.run ringId <| mkNonCommRingCnstr? e s kind lhs rhs
  else
    return some { kind, u := lhs, v := rhs }

def internalizeCnstr (e : Expr) (kind : CnstrKind) (lhs rhs : Expr) : OrderM Unit := do
  let some cnstr ← mkCnstr? e kind lhs rhs | return ()
  trace[grind.order.internalize] "{cnstr.u}, {cnstr.v}, {cnstr.k}"
  if grind.debug.get (← getOptions) then
    if let some h := cnstr.h? then check h

def hasLt : OrderM Bool :=
  return (← getStruct).ltFn?.isSome

public def internalize (e : Expr) (parent? : Option Expr) : GoalM Unit := do
  unless (← getConfig).order do return ()
  let some α := getType? e | return ()
  if isForbiddenParent parent? then return ()
  let some structId ← getStructId? α | return ()
  OrderM.run structId do
  match_expr e with
  | LE.le _ _ lhs rhs => internalizeCnstr e .le lhs rhs
  | LT.lt _ _ lhs rhs => if (← hasLt) then internalizeCnstr e .lt lhs rhs
  | Eq _ lhs rhs => internalizeCnstr e .eq lhs rhs
  | _ =>
    -- TODO
    return ()

end Lean.Meta.Grind.Order
