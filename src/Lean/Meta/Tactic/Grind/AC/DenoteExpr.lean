/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.AC.Util
import Lean.Meta.AppBuilder
public section
namespace Lean.Meta.Grind.AC
open Lean.Grind
variable [Monad M] [MonadGetStruct M] [MonadError M]

def _root_.Lean.Grind.AC.Seq.denoteExpr (s : AC.Seq) : M Expr := do
  match s with
  | .var x => return (← getStruct).vars[x]!
  | .cons x s => return mkApp2 (← getStruct).op (← getStruct).vars[x]! (← denoteExpr s)

def _root_.Lean.Grind.AC.Expr.denoteExpr (e : AC.Expr) : M Expr := do
  match e with
  | .var x => return (← getStruct).vars[x]!
  | .op lhs rhs => return mkApp2 (← getStruct).op (← denoteExpr lhs) (← denoteExpr rhs)

def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  let s ← getStruct
  return mkApp3 (mkConst ``Eq [s.u]) s.type (← c.lhs.denoteExpr) (← c.rhs.denoteExpr)

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  let s ← getStruct
  return mkApp3 (mkConst ``Ne [s.u]) s.type (← c.lhs.denoteExpr) (← c.rhs.denoteExpr)

end Lean.Meta.Grind.AC
