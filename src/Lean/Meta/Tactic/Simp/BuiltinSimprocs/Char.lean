/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ToExpr
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt

namespace Char
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option Char) :=
  getCharValue? e

@[inline] def reduceUnary [ToExpr α] (declName : Name) (op : Char → α) (arity : Nat := 1) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some c ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op c)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Char → Char → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Char → Char → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

builtin_dsimproc [simp, seval] reduceToLower (Char.toLower _) := reduceUnary ``Char.toLower Char.toLower
builtin_dsimproc [simp, seval] reduceToUpper (Char.toUpper _) := reduceUnary ``Char.toUpper Char.toUpper
builtin_dsimproc [simp, seval] reduceToNat (Char.toNat _) := reduceUnary ``Char.toNat Char.toNat
builtin_dsimproc [simp, seval] reduceIsWhitespace (Char.isWhitespace _) := reduceUnary ``Char.isWhitespace Char.isWhitespace
builtin_dsimproc [simp, seval] reduceIsUpper (Char.isUpper _) := reduceUnary ``Char.isUpper Char.isUpper
builtin_dsimproc [simp, seval] reduceIsLower (Char.isLower _) := reduceUnary ``Char.isLower Char.isLower
builtin_dsimproc [simp, seval] reduceIsAlpha (Char.isAlpha _) := reduceUnary ``Char.isAlpha Char.isAlpha
builtin_dsimproc [simp, seval] reduceIsDigit (Char.isDigit _) := reduceUnary ``Char.isDigit Char.isDigit
builtin_dsimproc [simp, seval] reduceIsAlphaNum (Char.isAlphanum _) := reduceUnary ``Char.isAlphanum Char.isAlphanum
builtin_dsimproc [simp, seval] reduceToString (toString (_ : Char)) := reduceUnary ``toString toString 3
builtin_dsimproc [simp, seval] reduceVal (Char.val _) := fun e => do
  let_expr Char.val arg ← e | return .continue
  let some c ← fromExpr? arg | return .continue
  return .done <| toExpr c.val

builtin_simproc [simp, seval] reduceLT  (( _ : Char) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Char) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Char) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Char) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : Char) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : Char) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] reduceBEq  (( _ : Char) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] reduceBNe  (( _ : Char) != _)  := reduceBoolPred ``bne 4 (. != .)

/--
Return `.done` for Char values. We don't want to unfold in the symbolic evaluator.
In regular `simp`, we want to prevent the nested raw literal from being converted into
a `OfNat.ofNat` application. TODO: cleanup
-/
builtin_dsimproc ↓ [simp, seval] isValue (Char.ofNat _ ) := fun e => do
  unless (← fromExpr? e).isSome do return .continue
  return .done e

builtin_dsimproc [simp, seval] reduceOfNatAux (Char.ofNatAux _ _) := fun e => do
  let_expr Char.ofNatAux n _ ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  return .done <| toExpr (Char.ofNat n)

builtin_dsimproc [simp, seval] reduceDefault ((default : Char)) := fun e => do
  let_expr default _ _ ← e | return .continue
  return .done <| toExpr (default : Char)

end Char
