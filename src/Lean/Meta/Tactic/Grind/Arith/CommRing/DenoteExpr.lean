/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Var

namespace Lean.Meta.Grind.Arith.CommRing
/-!
Helper functions for converting reified terms back into their denotations.
-/

private def denoteNum (k : Int) : RingM Expr := do
  let ring ← getRing
  let n := mkRawNatLit k.natAbs
  let ofNatInst := mkApp3 (mkConst ``Grind.CommRing.ofNat [ring.u]) ring.type ring.commRingInst n
  let n := mkApp3 (mkConst ``OfNat.ofNat [ring.u]) ring.type n ofNatInst
  if k < 0 then
    return mkApp ring.negFn n
  else
    return n

def _root_.Lean.Grind.CommRing.Power.denoteExpr (pw : Power) : RingM Expr := do
  let x := (← getRing).vars[pw.x]!
  if pw.k == 1 then
    return x
  else
    return mkApp2 (← getRing).powFn x (toExpr pw.k)

def _root_.Lean.Grind.CommRing.Mon.denoteExpr (m : Mon) : RingM Expr := do
  match m with
  | .unit => denoteNum 1
  | .mult pw m => go m (← pw.denoteExpr)
where
  go (m : Mon) (acc : Expr) : RingM Expr := do
    match m with
    | .unit => return acc
    | .mult pw m => go m (mkApp2 (← getRing).mulFn acc (← pw.denoteExpr))

def _root_.Lean.Grind.CommRing.Poly.denoteExpr (p : Poly) : RingM Expr := do
  match p with
  | .num k => denoteNum k
  | .add k m p => go p (← denoteTerm k m)
where
  denoteTerm (k : Int) (m : Mon) : RingM Expr := do
    if k == 1 then
      m.denoteExpr
    else
      return mkApp2 (← getRing).mulFn (← denoteNum k) (← m.denoteExpr)

  go (p : Poly) (acc : Expr) : RingM Expr := do
    match p with
    | .num 0 => return acc
    | .num k => return mkApp2 (← getRing).addFn acc (← denoteNum k)
    | .add k m p => go p (mkApp2 (← getRing).addFn acc (← denoteTerm k m))

def _root_.Lean.Grind.CommRing.Expr.denoteExpr (e : RingExpr) : RingM Expr := do
  go e
where
  go : RingExpr → RingM Expr
  | .num k => denoteNum k
  | .var x => return (← getRing).vars[x]!
  | .add a b => return mkApp2 (← getRing).addFn (← go a) (← go b)
  | .sub a b => return mkApp2 (← getRing).subFn (← go a) (← go b)
  | .mul a b => return mkApp2 (← getRing).mulFn (← go a) (← go b)
  | .pow a k => return mkApp2 (← getRing).powFn (← go a) (toExpr k)
  | .neg a => return mkApp (← getRing).negFn (← go a)

def EqCnstr.denoteExpr (c : EqCnstr) : RingM Expr := do
  mkEq (← c.p.denoteExpr) (← denoteNum 0)

def PolyDerivation.denoteExpr (d : PolyDerivation) : RingM Expr := do
  d.p.denoteExpr

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : RingM Expr := do
  return mkNot (← mkEq (← c.d.denoteExpr) (← denoteNum 0))

end Lean.Meta.Grind.Arith.CommRing
