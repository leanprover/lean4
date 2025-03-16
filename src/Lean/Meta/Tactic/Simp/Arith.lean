/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Meta.Tactic.Simp.Arith.Nat
import Lean.Meta.Tactic.Simp.Arith.Int

namespace Lean.Meta.Simp.Arith

def parentIsTarget (parent? : Option Expr) (isNatExpr : Bool) : Bool :=
  match parent? with
  | none => false
  | some parent => isLinearTerm parent isNatExpr || isLinearCnstr parent || isDvdCnstr parent

end Lean.Meta.Simp.Arith
