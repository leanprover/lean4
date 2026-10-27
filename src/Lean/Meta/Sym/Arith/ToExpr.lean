/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Init.Grind.Ring.CommSemiringAdapter
public import Lean.ToExpr
public section
namespace Lean.Meta.Sym.Arith
open Grind.CommRing
/-!
`ToExpr` instances for `CommRing.Poly` types. Numerals are constructor applications on raw
literals (`Int.ofNat n`, `Int.negSucc n`, and raw `Nat` literals), which the kernel evaluates
without unfolding `OfNat.ofNat` and `Neg.neg` when it checks certificates.
-/

/-- `k` as `Int.ofNat n` or `Int.negSucc n` on a raw literal. -/
def mkIntLitK (k : Int) : Expr :=
  match k with
  | .ofNat n => mkApp (mkConst ``Int.ofNat) (mkRawNatLit n)
  | .negSucc n => mkApp (mkConst ``Int.negSucc) (mkRawNatLit n)

def ofPower (p : Power) : Expr :=
  mkApp2 (mkConst ``Power.mk) (mkRawNatLit p.x) (mkRawNatLit p.k)

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
  | .num k => mkApp (mkConst ``Poly.num) (mkIntLitK k)
  | .add k m p => mkApp3 (mkConst ``Poly.add) (mkIntLitK k) (toExpr m) (ofPoly p)

instance : ToExpr Poly where
  toExpr := ofPoly
  toTypeExpr := mkConst ``Poly

open Lean.Grind

def ofRingExpr (e : CommRing.Expr) : Expr :=
  match e with
  | .num k => mkApp (mkConst ``CommRing.Expr.num) (mkIntLitK k)
  | .intCast k => mkApp (mkConst ``CommRing.Expr.intCast) (mkIntLitK k)
  | .natCast k => mkApp (mkConst ``CommRing.Expr.natCast) (mkRawNatLit k)
  | .var x => mkApp (mkConst ``CommRing.Expr.var) (mkRawNatLit x)
  | .add a b => mkApp2 (mkConst ``CommRing.Expr.add) (ofRingExpr a) (ofRingExpr b)
  | .mul a b => mkApp2 (mkConst ``CommRing.Expr.mul) (ofRingExpr a) (ofRingExpr b)
  | .sub a b => mkApp2 (mkConst ``CommRing.Expr.sub) (ofRingExpr a) (ofRingExpr b)
  | .neg a => mkApp (mkConst ``CommRing.Expr.neg) (ofRingExpr a)
  | .pow a k => mkApp2 (mkConst ``CommRing.Expr.pow) (ofRingExpr a) (mkRawNatLit k)

instance : ToExpr CommRing.Expr where
  toExpr := ofRingExpr
  toTypeExpr := mkConst ``CommRing.Expr

end Lean.Meta.Sym.Arith
