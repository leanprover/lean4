/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.LinearArith.Basic
import Lean.Meta.Tactic.LinearArith.Nat.Simp
import Lean.Meta.Tactic.LinearArith.Int.Simp

namespace Lean.Meta.Linear

def parentIsTarget (parent? : Option Expr) : Bool :=
  match parent? with
  | none => false
  | some parent => isLinearTerm parent || isLinearCnstr parent

def simp? (e : Expr) (parent? : Option Expr) : MetaM (Option (Expr × Expr)) := do
  -- TODO: add support for `Int` and arbitrary ordered comm rings
  if isLinearCnstr e then
    Nat.simpCnstr? e
  else if isLinearTerm e && !parentIsTarget parent? then
    trace[Meta.Tactic.simp] "arith expr: {e}"
    Nat.simpExpr? e
  else
    return none

end Lean.Meta.Linear
