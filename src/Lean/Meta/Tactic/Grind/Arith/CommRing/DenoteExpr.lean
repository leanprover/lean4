/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
public import Lean.Meta.Sym.Arith.DenoteExpr
public section
namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith
/-!
Dot-notation entry points to `Sym.Arith` denotation, plus denotation of the solver's constraints.
-/

variable [Monad M] [MonadError M] [MonadLiftT MetaM M] [MonadCanon M] [MonadRing M]

def _root_.Lean.Grind.CommRing.Expr.denoteExpr' (vars : Array Expr) (e : RingExpr) : M Expr :=
  denoteRingExpr' vars e

section
variable [MonadGetVar M]

def _root_.Lean.Grind.CommRing.Power.denoteExpr (pw : Power) : M Expr :=
  denotePower pw

def _root_.Lean.Grind.CommRing.Mon.denoteExpr (m : Mon) : M Expr :=
  denoteMon m

def _root_.Lean.Grind.CommRing.Poly.denoteExpr (p : Poly) : M Expr :=
  denotePoly p

def _root_.Lean.Grind.CommRing.Expr.denoteExpr (e : RingExpr) : M Expr :=
  denoteRingExpr e

private def mkEq (a b : Expr) : M Expr := do
  let r ← getRing
  return mkApp3 (mkConst ``Eq [r.u.succ]) r.type a b

def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  mkEq (← c.p.denoteExpr) (← denoteNum 0)

def PolyDerivation.denoteExpr (d : PolyDerivation) : M Expr := do
  d.p.denoteExpr

def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  return mkNot (← mkEq (← c.d.denoteExpr) (← denoteNum 0))

end

end Lean.Meta.Grind.Arith.CommRing
