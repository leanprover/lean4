/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Grind.Arith

/-- Applies `a^(m+n) = a^m * a^n` -/
builtin_simproc_decl reducePowAdd ((_ ^ _ : Nat)) := fun e => do
  let_expr HPow.hPow _ _ _ _ a k := e | return .continue
  let_expr HAdd.hAdd _ _ _ _ m n := k | return .continue
  let r := mkNatMul (mkNatPow a m) (mkNatPow a n)
  let h := mkApp3 (mkConst ``Nat.pow_add) a m n
  return .visit { expr := r, proof? := some h }

def addSimproc (s : Simprocs) : CoreM Simprocs := do
  s.add ``reducePowAdd (post := true)

end Lean.Meta.Grind.Arith
