/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.CommRing.Poly
import Lean.ToExpr

namespace Lean.Meta.Grind.Arith.CommRing
open Grind.CommRing
/-!
`ToExpr` instances for `CommRing.Poly` types.
-/

def ofPower (p : Power) : Expr :=
  mkApp2 (mkConst ``Power.mk) (toExpr p.x) (toExpr p.k)

instance : ToExpr Power where
  toExpr := ofPower
  toTypeExpr := mkConst ``Power

def ofMon (m : Mon) : Expr :=
  match m with
  | .unit => mkConst ``Mon.unit
  | .mult pw m => mkApp2 (mkConst ``Mon.mult) (toExpr pw) (ofMon m)

instance : ToExpr Mon where
  toExpr := ofMon
  toTypeExpr := mkConst ``Mon

def ofPoly (p : Poly) : Expr :=
  match p with
  | .num k => mkApp (mkConst ``Poly.num) (toExpr k)
  | .add k m p => mkApp3 (mkConst ``Poly.add) (toExpr k) (toExpr m) (ofPoly p)

instance : ToExpr Poly where
  toExpr := ofPoly
  toTypeExpr := mkConst ``Poly

open Lean.Grind

def ofRingExpr (e : CommRing.Expr) : Expr :=
  match e with
  | .num k => mkApp (mkConst ``CommRing.Expr.num) (toExpr k)
  | .var x => mkApp (mkConst ``CommRing.Expr.var) (toExpr x)
  | .add a b => mkApp2 (mkConst ``CommRing.Expr.add) (ofRingExpr a) (ofRingExpr b)
  | .mul a b => mkApp2 (mkConst ``CommRing.Expr.mul) (ofRingExpr a) (ofRingExpr b)
  | .sub a b => mkApp2 (mkConst ``CommRing.Expr.sub) (ofRingExpr a) (ofRingExpr b)
  | .neg a => mkApp (mkConst ``CommRing.Expr.neg) (ofRingExpr a)
  | .pow a k => mkApp2 (mkConst ``CommRing.Expr.pow) (ofRingExpr a) (toExpr k)

instance : ToExpr CommRing.Expr where
  toExpr := ofRingExpr
  toTypeExpr := mkConst ``CommRing.Expr

def ofNullCert (nc : NullCert) : Expr :=
  match nc with
  | .empty => mkConst ``CommRing.NullCert.empty
  | .add q lhs rhs nc => mkApp4 (mkConst ``CommRing.NullCert.add) (toExpr q) (toExpr lhs) (toExpr rhs) (ofNullCert nc)

instance : ToExpr CommRing.NullCert where
  toExpr := ofNullCert
  toTypeExpr := mkConst ``CommRing.NullCert

end Lean.Meta.Grind.Arith.CommRing
