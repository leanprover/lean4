/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ToExpr
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt

namespace Char
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option Char) := OptionT.run do
  guard (e.isAppOfArity ``Char.ofNat 1)
  let value ← Nat.fromExpr? e.appArg!
  return Char.ofNat value

@[inline] def reduceUnary [ToExpr α] (declName : Name) (op : Char → α) (arity : Nat := 1) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some c ← fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (op c) }

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Char → Char → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Char → Char → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done { expr := toExpr (op n m) }

builtin_simproc [simp, seval] reduceToLower (Char.toLower _) := reduceUnary ``Char.toLower Char.toLower
builtin_simproc [simp, seval] reduceToUpper (Char.toUpper _) := reduceUnary ``Char.toUpper Char.toUpper
builtin_simproc [simp, seval] reduceToNat (Char.toNat _) := reduceUnary ``Char.toNat Char.toNat
builtin_simproc [simp, seval] reduceIsWhitespace (Char.isWhitespace _) := reduceUnary ``Char.isWhitespace Char.isWhitespace
builtin_simproc [simp, seval] reduceIsUpper (Char.isUpper _) := reduceUnary ``Char.isUpper Char.isUpper
builtin_simproc [simp, seval] reduceIsLower (Char.isLower _) := reduceUnary ``Char.isLower Char.isLower
builtin_simproc [simp, seval] reduceIsAlpha (Char.isAlpha _) := reduceUnary ``Char.isAlpha Char.isAlpha
builtin_simproc [simp, seval] reduceIsDigit (Char.isDigit _) := reduceUnary ``Char.isDigit Char.isDigit
builtin_simproc [simp, seval] reduceIsAlphaNum (Char.isAlphanum _) := reduceUnary ``Char.isAlphanum Char.isAlphanum
builtin_simproc [simp, seval] reduceToString (toString (_ : Char)) := reduceUnary ``toString toString 3
builtin_simproc [simp, seval] reduceVal (Char.val _) := fun e => do
  unless e.isAppOfArity ``Char.val 1 do return .continue
  let some c ← fromExpr? e.appArg! | return .continue
  return .done { expr := UInt32.toExprCore c.val }
builtin_simproc [simp, seval] reduceEq  (( _ : Char) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : Char) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_simproc [simp, seval] reduceBEq  (( _ : Char) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_simproc [simp, seval] reduceBNe  (( _ : Char) != _)  := reduceBoolPred ``bne 4 (. != .)

/--
Return `.done` for Char values. We don't want to unfold in the symbolic evaluator.
In regular `simp`, we want to prevent the nested raw literal from being converted into
a `OfNat.ofNat` application. TODO: cleanup
-/
builtin_simproc ↓ [simp, seval] isValue (Char.ofNat _ ) := fun e => do
  unless (← fromExpr? e).isSome do return .continue
  return .done { expr := e }

builtin_simproc [simp, seval] reduceOfNatAux (Char.ofNatAux _ _) := fun e => do
  unless e.isAppOfArity ``Char.ofNatAux 2 do return .continue
  let some n ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  return .done { expr := toExpr (Char.ofNat n) }

builtin_simproc [simp, seval] reduceDefault ((default : Char)) := fun e => do
  unless e.isAppOfArity ``default 2 do return .continue
  return .done { expr := toExpr (default : Char) }

end Char
