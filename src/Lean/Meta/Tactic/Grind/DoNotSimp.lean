/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Util
import Init.Simproc
import Lean.Meta.Tactic.Simp.Simproc

namespace Lean.Meta.Grind

/--
Returns `Grind.doNotSimp e`.
Recall that `Grind.doNotSimp` is an identity function, but the following simproc is used to prevent the term `e` from being simplified.
-/
def markAsDoNotSimp (e : Expr) : MetaM Expr :=
  mkAppM ``Grind.doNotSimp #[e]

builtin_dsimproc_decl reduceDoNotSimp (Grind.doNotSimp _) := fun e => do
  let_expr Grind.doNotSimp _ _ ← e | return .continue
  return .done e

/-- Adds `reduceDoNotSimp` to `s` -/
def addDoNotSimp (s : Simprocs) : CoreM Simprocs := do
  s.add ``reduceDoNotSimp (post := false)

/-- Erases `Grind.doNotSimp` annotations. -/
def eraseDoNotSimp (e : Expr) : CoreM Expr := do
  let pre (e : Expr) := do
    let_expr Grind.doNotSimp _ a := e | return .continue e
    return .continue a
  Core.transform e (pre := pre)

end Lean.Meta.Grind
