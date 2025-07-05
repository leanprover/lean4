/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Ring.Basic
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Grind.SynthInstance

namespace Lean.Meta.Grind.Arith

private def mkSemiringThm (declName : Name) (α : Expr) : MetaM (Option Expr) := do
  let some u ← getDecLevel? α | return none
  let semiring := mkApp (mkConst ``Grind.Semiring [u]) α
  let some semiringInst ← synthInstanceMeta? semiring | return none
  return mkApp2 (mkConst declName [u]) α semiringInst

/--
Applies `a^(m+n) = a^m * a^n`, `a^0 = 1`, `a^1 = a`.

We do normalize `a^0` and `a^1` when converting expressions into polynomials,
but we need to normalize them here when for other preprocessing steps such as
`a / b = a*b⁻¹`. If `b` is of the form `c^1`, it will be treated as an
atom in the comm ring module.
-/
builtin_simproc_decl expandPowAdd (_ ^ _) := fun e => do
  let_expr HPow.hPow α nat α' _ a k := e | return .continue
  let_expr Nat ← nat | return .continue
  if let some k ← getNatValue? k then
    if k == 0 then
      unless (← isDefEq α α') do return .continue
      let some h ← mkSemiringThm ``Grind.Semiring.pow_zero α | return .continue
      let r ← mkNumeral α 1
      return .done { expr := r, proof? := some (mkApp h a) }
    else if k == 1 then
      unless (← isDefEq α α') do return .continue
      let some h ← mkSemiringThm ``Grind.Semiring.pow_one α | return .continue
      return .done { expr := a, proof? := some (mkApp h a) }
    else
      return .continue
  else
    let_expr HAdd.hAdd _ _ _ _ m n := k | return .continue
    unless (← isDefEq α α') do return .continue
    let some h ← mkSemiringThm ``Grind.Semiring.pow_add α | return .continue
    let pwFn := e.appFn!.appFn!
    let r ← mkMul (mkApp2 pwFn a m) (mkApp2 pwFn a n)
    return .visit { expr := r, proof? := some (mkApp3 h a m n) }

def addSimproc (s : Simprocs) : CoreM Simprocs := do
  s.add ``expandPowAdd (post := true)

end Lean.Meta.Grind.Arith
