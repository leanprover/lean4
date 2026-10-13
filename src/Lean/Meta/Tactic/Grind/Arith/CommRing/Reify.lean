/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
public import Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommSemiringM
public import Lean.Meta.Sym.Arith.Reify
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith

/-!
Reification is implemented by `Sym.Arith.reifyRing?` and `Sym.Arith.reifySemiring?`.
-/

/-- Reify ring expression. -/
def reify? (e : Expr) (skipVar := true) : RingM (Option RingExpr) :=
  reifyRing? e skipVar

/-- Reify non-commutative ring expression. -/
def ncreify? (e : Expr) (skipVar := true) : NonCommRingM (Option RingExpr) :=
  reifyRing? e skipVar

/-- Reify semiring expression. -/
def sreify? (e : Expr) : SemiringM (Option SemiringExpr) :=
  reifySemiring? e

/-- Reify non-commutative semiring expression. -/
def ncsreify? (e : Expr) : NonCommSemiringM (Option SemiringExpr) :=
  reifySemiring? e

end Lean.Meta.Grind.Arith.CommRing
