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
Returns `Grind.MatchCond e`.
Recall that `Grind.MatchCond` is an identity function,
but the following simproc is used to prevent the term `e` from being simplified,
and we have special support for propagating is truth value.
-/
def markAsMatchCond (e : Expr) : MetaM Expr :=
  mkAppM ``Grind.MatchCond #[e]

builtin_dsimproc_decl reduceMatchCond (Grind.MatchCond _) := fun e => do
  let_expr Grind.MatchCond _ ← e | return .continue
  return .done e

/-- Adds `reduceMatchCond` to `s` -/
def addMatchCond (s : Simprocs) : CoreM Simprocs := do
  s.add ``reduceMatchCond (post := false)

end Lean.Meta.Grind
