/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ordered.Linarith
public import Lean.ToExpr
public section
namespace Lean.Meta.Grind.Arith.Linear
open Grind.Linarith
/-!
`ToExpr` instances for linear expressions and polynomials. Coefficients and indices use raw
literals and integer constructors so that certificate checking avoids overloaded numerals.
-/

private def ofInt (k : Int) : Expr :=
  match k with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

def ofPoly (p : Poly) : Expr :=
  match p with
  | .nil => mkConst ``Poly.nil
  | .add k x p => mkApp3 (mkConst ``Poly.add) (ofInt k) (mkRawNatLit x) (ofPoly p)

instance : ToExpr Poly where
  toExpr := ofPoly
  toTypeExpr := mkConst ``Poly

open Lean.Grind

def ofLinExpr (e : Linarith.Expr) : Expr :=
  match e with
  | .zero => mkConst ``Linarith.Expr.zero
  | .var x => mkApp (mkConst ``Linarith.Expr.var) (mkRawNatLit x)
  | .add a b => mkApp2 (mkConst ``Linarith.Expr.add) (ofLinExpr a) (ofLinExpr b)
  | .sub a b => mkApp2 (mkConst ``Linarith.Expr.sub) (ofLinExpr a) (ofLinExpr b)
  | .neg a => mkApp (mkConst ``Linarith.Expr.neg) (ofLinExpr a)
  | .natMul k a => mkApp2 (mkConst ``Linarith.Expr.natMul) (mkRawNatLit k) (ofLinExpr a)
  | .intMul k a => mkApp2 (mkConst ``Linarith.Expr.intMul) (ofInt k) (ofLinExpr a)

instance : ToExpr Linarith.Expr where
  toExpr := ofLinExpr
  toTypeExpr := mkConst ``Linarith.Expr

end Lean.Meta.Grind.Arith.Linear
