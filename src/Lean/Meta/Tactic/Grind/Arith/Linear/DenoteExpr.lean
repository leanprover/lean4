/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Grind.ProveEq
import Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr
import Lean.Meta.Tactic.Grind.Arith.Linear.Util
import Lean.Meta.Tactic.Grind.Arith.Linear.Var

namespace Lean.Meta.Grind.Arith.Linear
/-!
Helper functions for converting reified terms back into their denotations.
-/

variable [Monad M] [MonadGetStruct M] [MonadError M]

def _root_.Lean.Grind.Linarith.Poly.denoteExpr (p : Poly) : M Expr := do
  match p with
  | .nil => return (← getStruct).zero
  | .add k x p => go p (← denoteTerm k x)
where
  denoteTerm (k : Int) (x : Var) : M Expr := do
    if k == 1 then
      return (← getStruct).vars[x]!
    else
      return mkApp2 (← getStruct).hmulFn (mkIntLit k) (← getStruct).vars[x]!

  go (p : Poly) (acc : Expr) : M Expr := do
    match p with
    | .nil => return acc
    | .add k m p => go p (mkApp2 (← getStruct).addFn acc (← denoteTerm k m))

def _root_.Lean.Grind.Linarith.Expr.denoteExpr (e : LinExpr) : M Expr := do
  go e
where
  go : LinExpr → M Expr
  | .zero => return (← getStruct).zero
  | .var x => return (← getStruct).vars[x]!
  | .add a b => return mkApp2 (← getStruct).addFn (← go a) (← go b)
  | .sub a b => return mkApp2 (← getStruct).subFn (← go a) (← go b)
  | .mul k a => return mkApp2 (← getStruct).hmulFn (mkIntLit k) (← go a)
  | .neg a => return mkApp (← getStruct).negFn (← go a)

private def mkEq (a b : Expr) : M Expr := do
  let s ← getStruct
  return mkApp3 (mkConst ``Eq [s.u.succ]) s.type a b

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  return mkNot (← mkEq (← c.p.denoteExpr) (← getStruct).ofNatZero)

private def denoteIneq (p : Poly) (strict : Bool) : M Expr := do
  if strict then
    return mkApp2 (← getLtFn) (← p.denoteExpr) (← getStruct).ofNatZero
  else
    return mkApp2 (← getLeFn) (← p.denoteExpr) (← getStruct).ofNatZero

def IneqCnstr.denoteExpr (c : IneqCnstr) : M Expr := do
  denoteIneq c.p c.strict

def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  mkEq (← c.p.denoteExpr) (← getStruct).ofNatZero

private def denoteNum (k : Int) : LinearM Expr := do
  return mkApp2 (← getStruct).hmulFn (mkIntLit k) (← getOne)

def _root_.Lean.Grind.CommRing.Poly.denoteAsIntModuleExpr (p : Grind.CommRing.Poly) : LinearM Expr := do
  match p with
  | .num k => denoteNum k
  | .add k m p => return mkApp2 (← getStruct).addFn (mkApp2 (← getStruct).hmulFn (mkIntLit k) (← m.denoteExpr)) (← denoteAsIntModuleExpr p)

def _root_.Lean.Grind.CommRing.Poly.toIntModuleExpr (p : Grind.CommRing.Poly) (generation := 0) : LinearM Expr := do
  let e ← p.denoteAsIntModuleExpr
  let e ← preprocessLight e
  internalize e generation (some getIntModuleVirtualParent)
  return e

end Lean.Meta.Grind.Arith.Linear
