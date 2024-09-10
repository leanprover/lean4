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

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : String → String → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : String → String → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

builtin_simproc [simp, seval] reduceLT  (( _ : String) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : String) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : String) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : String) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : String) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : String) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] reduceBEq  (( _ : String) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] reduceBNe  (( _ : String) != _)  := reduceBoolPred ``bne 4 (. != .)

end String
