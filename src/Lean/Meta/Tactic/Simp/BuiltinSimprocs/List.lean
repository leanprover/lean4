/-
Copyright (c) 2024 Lean FRO. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

namespace List
open Lean Meta Simp

/-- Simplification procedure for `List.replicate` applied to a `Nat` literal. -/
-- We don't always want `List.replicate_succ` as a `simp` lemma,
-- so we use this `dsimproc` to unfold `List.replicate` applied to literals.
builtin_dsimproc [simp, seval] reduceReplicate (replicate _ _) := fun e => do
  let_expr replicate α n x ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  return .done <| (← mkListLit α (List.replicate n x))

end List
