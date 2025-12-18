/-
Copyright (c) 2022 Sebastian Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Meta.Tactic.Simp.Arith.Nat
public import Lean.Meta.Tactic.Simp.Arith.Int

public section

namespace Lean.Meta.Simp.Arith

def parentIsTarget (parent? : Option Expr) : Bool :=
  match parent? with
  | none => false
  | some parent => isLinearTerm parent || isLinearCnstr parent || isDvdCnstr parent

end Lean.Meta.Simp.Arith
