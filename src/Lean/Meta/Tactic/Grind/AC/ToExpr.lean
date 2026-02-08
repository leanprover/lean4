/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.AC
public import Lean.ToExpr
public section
namespace Lean.Meta.Grind.AC
open Lean.Grind
/-!
`ToExpr` instances for `AC` types.
-/
def ofSeq (m : AC.Seq) : Expr :=
  match m with
  | .var x => mkApp (mkConst ``AC.Seq.var) (toExpr x)
  | .cons x s => mkApp2 (mkConst ``AC.Seq.cons) (toExpr x) (ofSeq s)

instance : ToExpr AC.Seq where
  toExpr := ofSeq
  toTypeExpr := mkConst ``AC.Seq

def ofExpr (m : AC.Expr) : Expr :=
  match m with
  | .var x => mkApp (mkConst ``AC.Expr.var) (toExpr x)
  | .op lhs rhs => mkApp2 (mkConst ``AC.Expr.op) (ofExpr lhs) (ofExpr rhs)

instance : ToExpr AC.Expr where
  toExpr := ofExpr
  toTypeExpr := mkConst ``AC.Expr

end Lean.Meta.Grind.AC
