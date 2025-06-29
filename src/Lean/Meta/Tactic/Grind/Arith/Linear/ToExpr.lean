/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Ordered.Linarith
import Lean.ToExpr

namespace Lean.Meta.Grind.Arith.Linear
open Grind.Linarith

/-!
`ToExpr` instances for `Linarith.Poly` types.
-/

def ofPoly (p : Poly) : Expr :=
  match p with
  | .nil => mkConst ``Poly.nil
  | .add k x p => mkApp3 (mkConst ``Poly.add) (toExpr k) (toExpr x) (ofPoly p)

instance : ToExpr Poly where
  toExpr := ofPoly
  toTypeExpr := mkConst ``Poly

open Lean.Grind

def ofLinExpr (e : Linarith.Expr) : Expr :=
  match e with
  | .zero => mkConst ``Linarith.Expr.zero
  | .var x => mkApp (mkConst ``Linarith.Expr.var) (toExpr x)
  | .add a b => mkApp2 (mkConst ``Linarith.Expr.add) (ofLinExpr a) (ofLinExpr b)
  | .sub a b => mkApp2 (mkConst ``Linarith.Expr.sub) (ofLinExpr a) (ofLinExpr b)
  | .neg a => mkApp (mkConst ``Linarith.Expr.neg) (ofLinExpr a)
  | .natMul k a => mkApp2 (mkConst ``Linarith.Expr.natMul) (toExpr k) (ofLinExpr a)
  | .intMul k a => mkApp2 (mkConst ``Linarith.Expr.intMul) (toExpr k) (ofLinExpr a)

instance : ToExpr Linarith.Expr where
  toExpr := ofLinExpr
  toTypeExpr := mkConst ``Linarith.Expr

end Lean.Meta.Grind.Arith.Linear
