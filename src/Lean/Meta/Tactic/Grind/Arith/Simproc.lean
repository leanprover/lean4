/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Ring.Basic
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Grind.Arith

/-- Applies `a^(m+n) = a^m * a^n` -/
builtin_simproc_decl expandPowAdd (_ ^ _) := fun e => do
  let_expr HPow.hPow α nat α' _ a k := e | return .continue
  let_expr HAdd.hAdd _ _ _ _ m n := k | return .continue
  let_expr Nat ← nat | return .continue
  unless (← isDefEq α α') do return .continue
  let u ← getLevel α
  let some u ← decLevel? u | return .continue
  let semiring := mkApp (mkConst ``Grind.Semiring [u]) α
  let .some semiringInst ← trySynthInstance semiring | return .continue
  let pwFn := e.appFn!.appFn!
  let r ← mkMul (mkApp2 pwFn a m) (mkApp2 pwFn a n)
  let h := mkApp5 (mkConst ``Grind.Semiring.pow_add [u]) α semiringInst a m n
  return .visit { expr := r, proof? := some h }

def addSimproc (s : Simprocs) : CoreM Simprocs := do
  s.add ``expandPowAdd (post := true)

end Lean.Meta.Grind.Arith
