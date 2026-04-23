/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Tactic.Grind.Arith.CommRing.Types
public import Lean.Meta.Sym.Arith.DenoteExpr

namespace Lean.Meta.Grind.Arith.CommRing
open Sym.Arith
/-!
Helper functions for converting reified terms back into their denotations.
-/

variable [Monad M] [MonadGetVar M] [MonadError M] [MonadLiftT MetaM M] [MonadCanon M] [MonadRing M]

def mkEq (a b : Expr) : M Expr := do
  let r ← getRing
  return mkApp3 (mkConst ``Eq [r.u.succ]) r.type a b

public def EqCnstr.denoteExpr (c : EqCnstr) : M Expr := do
  mkEq (← denotePoly c.p) (← denoteNum 0)

public def PolyDerivation.denoteExpr (d : PolyDerivation) : M Expr := do
  denotePoly d.p

public def DiseqCnstr.denoteExpr (c : DiseqCnstr) : M Expr := do
  return mkNot (← mkEq (← c.d.denoteExpr) (← denoteNum 0))

end Lean.Meta.Grind.Arith.CommRing
