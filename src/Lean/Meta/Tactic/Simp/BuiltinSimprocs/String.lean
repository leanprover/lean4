/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ToExpr
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Char

namespace String
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option String) := do
  return getStringValue? e

builtin_dsimproc [simp, seval] reduceAppend ((_ ++ _ : String)) := fun e => do
  unless e.isAppOfArity ``HAppend.hAppend 6 do return .continue
  let some a ← fromExpr? e.appFn!.appArg! | return .continue
  let some b ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (a ++ b)

private partial def reduceListChar (e : Expr) (s : String) : SimpM DStep := do
  if e.isAppOfArity ``List.nil 1 then
    return .done <| toExpr s
  else if e.isAppOfArity ``List.cons 3 then
    let some c ← Char.fromExpr? e.appFn!.appArg! | return .continue
    reduceListChar e.appArg! (s.push c)
  else
    return .continue

builtin_dsimproc [simp, seval] reduceMk (String.mk _) := fun e => do
  unless e.isAppOfArity ``String.mk 1 do return .continue
  reduceListChar e.appArg! ""

end String
