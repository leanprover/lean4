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

private def denoteNum (ring : Ring) (k : Int) : MetaM Expr := do
  return mkApp ring.intCastFn (toExpr k)

def _root_.Lean.Grind.CommRing.Power.denoteExpr' (ring : Ring) (pw : Power) : MetaM Expr := do
  let x := ring.vars[pw.x]!
  if pw.k == 1 then
    return x
  else
    return mkApp2 ring.powFn x (toExpr pw.k)

def _root_.Lean.Grind.CommRing.Mon.denoteExpr' (ring : Ring) (m : Mon) : MetaM Expr := do
  match m with
  | .unit => denoteNum ring 1
  | .mult pw m => go m (← pw.denoteExpr' ring)
where
  go (m : Mon) (acc : Expr) : MetaM Expr := do
    match m with
    | .unit => return acc
    | .mult pw m => go m (mkApp2 ring.mulFn acc (← pw.denoteExpr' ring))

def _root_.Lean.Grind.CommRing.Poly.denoteExpr' (ring : Ring) (p : Poly) : MetaM Expr := do
  match p with
  | .num k => denoteNum ring k
  | .add k m p => go p (← denoteTerm k m)
where
  denoteTerm (k : Int) (m : Mon) : MetaM Expr := do
    if k == 1 then
      m.denoteExpr' ring
    else
      return mkApp2 ring.mulFn (← denoteNum ring k) (← m.denoteExpr' ring)

  go (p : Poly) (acc : Expr) : MetaM Expr := do
    match p with
    | .num 0 => return acc
    | .num k => return mkApp2 ring.addFn acc (← denoteNum ring k)
    | .add k m p => go p (mkApp2 ring.addFn acc (← denoteTerm k m))

def _root_.Lean.Grind.CommRing.Expr.denoteExpr' (ring : Ring) (e : RingExpr) : MetaM Expr := do
  go e
where
  go : RingExpr → MetaM Expr
  | .num k => denoteNum ring k
  | .var x => return ring.vars[x]!
  | .add a b => return mkApp2 ring.addFn (← go a) (← go b)
  | .sub a b => return mkApp2 ring.subFn (← go a) (← go b)
  | .mul a b => return mkApp2 ring.mulFn (← go a) (← go b)
  | .pow a k => return mkApp2 ring.powFn (← go a) (toExpr k)
  | .neg a => return mkApp ring.negFn (← go a)

def _root_.Lean.Grind.CommRing.Power.denoteExpr (ringId : Nat) (pw : Power) : GoalM Expr := do
  pw.denoteExpr' (← getRing ringId)

def _root_.Lean.Grind.CommRing.Mon.denoteExpr (ringId : Nat) (m : Mon) : GoalM Expr := do
  m.denoteExpr' (← getRing ringId)

def _root_.Lean.Grind.CommRing.Poly.denoteExpr (ringId : Nat) (p : Poly) : GoalM Expr := do
  p.denoteExpr' (← getRing ringId)

def _root_.Lean.Grind.CommRing.Expr.denoteExpr (ringId : Nat) (e : RingExpr) : GoalM Expr := do
  e.denoteExpr' (← getRing ringId)

end Lean.Meta.Grind.Arith.CommRing
