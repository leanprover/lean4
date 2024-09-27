/-
Copyright (c) 2024 Lean FRO. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

namespace Array
open Lean Meta Simp

/-- Simplification procedure for `#[...][n]` for `n` a `Nat` literal. -/
builtin_dsimproc [simp, seval] reduceGetElem (@GetElem.getElem (Array _) Nat _ _ _ _ _ _) := fun e => do
  let_expr GetElem.getElem _ _ _ _ _ xs n _ ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  let some xs ← getArrayLit? xs | return .continue
  return .done <| xs[n]!

/-- Simplification procedure for `#[...][n]?` for `n` a `Nat` literal. -/
builtin_dsimproc [simp, seval] reduceGetElem? (@GetElem?.getElem? (Array _) Nat _ _ _ _ _) := fun e => do
  let_expr GetElem?.getElem? _ _ α _ _ xs n ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  let some xs ← getArrayLit? xs | return .continue
  let r ← if h : n < xs.size then mkSome α xs[n] else mkNone α
  return .done r

/-- Simplification procedure for `#[...][n]!` for `n` a `Nat` literal. -/
builtin_dsimproc [simp, seval] reduceGetElem! (@GetElem?.getElem! (Array _) Nat _ _ _ _ _ _) := fun e => do
  let_expr GetElem?.getElem! _ _ α _ _ _ xs n ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  let some xs ← getArrayLit? xs | return .continue
  let r ← if h : n < xs.size then pure xs[n] else mkDefault α
  return .done r

end Array
