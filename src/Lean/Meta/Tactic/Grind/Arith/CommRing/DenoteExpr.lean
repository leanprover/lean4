/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.Arith.CommRing.Util
import Lean.Meta.Tactic.Grind.Arith.CommRing.Var
import Lean.Meta.Tactic.Grind.Arith.CommRing.RingId

namespace Lean.Meta.Grind.Arith.CommRing
/-!
Helper functions for converting reified terms back into their denotations.
-/

variable [Monad M] [MonadGetRing M]

def denoteNum (k : Int) : M Expr := do
  let ring ← getRing
  return denoteNumCore ring.u ring.type ring.semiringInst ring.negFn k

def _root_.Lean.Grind.CommRing.Power.denoteExpr (pw : Power) : M Expr := do
  let x := (← getRing).vars[pw.x]!
  if pw.k == 1 then
    return x
  else
    return mkApp2 (← getRing).powFn x (toExpr pw.k)

def _root_.Lean.Grind.CommRing.Mon.denoteExpr (m : Mon) : M Expr := do
  match m with
  | .unit => denoteNum 1
  | .mult pw m => go m (← pw.denoteExpr)
where
  go (m : Mon) (acc : Expr) : M Expr := do
    match m with
    | .unit => return acc
    | .mult pw m => go m (mkApp2 (← getRing).mulFn acc (← pw.denoteExpr))

def _root_.Lean.Grind.CommRing.Poly.denoteExpr (p : Poly) : M Expr := do
  match p with
  | .num k => denoteNum k
  | .add k m p => go p (← denoteTerm k m)
where
  denoteTerm (k : Int) (m : Mon) : M Expr := do
    if k == 1 then
      m.denoteExpr
    else
      return mkApp2 (← getRing).mulFn (← denoteNum k) (← m.denoteExpr)

  go (p : Poly) (acc : Expr) : M Expr := do
    match p with
    | .num 0 => return acc
    | .num k => return mkApp2 (← getRing).addFn acc (← denoteNum k)
    | .add k m p => go p (mkApp2 (← getRing).addFn acc (← denoteTerm k m))

def _root_.Lean.Grind.CommRing.Expr.denoteExpr (e : RingExpr) : M Expr := do
  go e
where
  go : RingExpr → M Expr
  | .num k => denoteNum k
  | .var x => return (← getRing).vars[x]!
  | .add a b => return mkApp2 (← getRing).addFn (← go a) (← go b)
  | .sub a b => return mkApp2 (← getRing).subFn (← go a) (← go b)
  | .mul a b => return mkApp2 (← getRing).mulFn (← go a) (← go b)
  | .pow a k => return mkApp2 (← getRing).powFn (← go a) (toExpr k)
  | .neg a => return mkApp (← getRing).negFn (← go a)

private def mkEq (a b : Expr) : M Expr := do
  let r ← getRing
  return mkApp3 (mkConst ``Eq [r.u.succ]) r.type a b

def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  mkEq (← c.p.denoteExpr) (← denoteNum 0)

def PolyDerivation.denoteExpr (d : PolyDerivation) : M Expr := do
  d.p.denoteExpr

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  return mkNot (← mkEq (← c.d.denoteExpr) (← denoteNum 0))

end Lean.Meta.Grind.Arith.CommRing
