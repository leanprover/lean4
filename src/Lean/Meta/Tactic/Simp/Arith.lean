/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Meta.Tactic.Simp.Arith.Nat
import Lean.Meta.Tactic.Simp.Arith.Int

namespace Lean.Meta.Simp.Arith

def parentIsTarget (parent? : Option Expr) : Bool :=
  match parent? with
  | none => false
  | some parent => isLinearTerm parent || isLinearCnstr parent || isDvdCnstr parent

def simp? (e : Expr) (parent? : Option Expr) : MetaM (Option (Expr × Expr)) := do
  -- TODO: invoke `Int` procedures and add support for arbitrary ordered comm rings
  if isLinearCnstr e then
    Nat.simpCnstr? e
  else if isLinearTerm e && !parentIsTarget parent? then
    trace[Meta.Tactic.simp] "arith expr: {e}"
    Nat.simpExpr? e
  else
    return none

end Lean.Meta.Simp.Arith
