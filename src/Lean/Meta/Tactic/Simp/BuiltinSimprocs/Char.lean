/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.UInt

public section

namespace Lean.Char
open Meta Simp

@[inherit_doc getCharValue?]
def fromExpr? (e : Expr) : SimpM (Option Char) :=
  getCharValue? e

end Lean.Char

namespace Char
open Lean Meta Simp Lean.Char

@[inline] private def reduceUnary [ToExpr α] (declName : Name) (op : Char → α) (arity : Nat := 1) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some c ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op c)

@[inline] private def reduceBinPred (declName : Name) (arity : Nat) (op : Char → Char → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op n m)

@[inline] private def reduceBoolPred (declName : Name) (arity : Nat) (op : Char → Char → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceToLower (Char.toLower _) := reduceUnary ``Char.toLower Char.toLower
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceToUpper (Char.toUpper _) := reduceUnary ``Char.toUpper Char.toUpper
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceToNat (Char.toNat _) := reduceUnary ``Char.toNat Char.toNat
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceIsWhitespace (Char.isWhitespace _) := reduceUnary ``Char.isWhitespace Char.isWhitespace
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceIsUpper (Char.isUpper _) := reduceUnary ``Char.isUpper Char.isUpper
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceIsLower (Char.isLower _) := reduceUnary ``Char.isLower Char.isLower
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceIsAlpha (Char.isAlpha _) := reduceUnary ``Char.isAlpha Char.isAlpha
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceIsDigit (Char.isDigit _) := reduceUnary ``Char.isDigit Char.isDigit
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceIsAlphaNum (Char.isAlphanum _) := reduceUnary ``Char.isAlphanum Char.isAlphanum
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceToString (toString (_ : Char)) := reduceUnary ``toString toString 3
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceVal (Char.val _) := fun e => do
  let_expr Char.val arg ← e | return .continue
  let some c ← fromExpr? arg | return .continue
  return .done <| toExpr c.val

set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_simproc [simp, seval] reduceLT  (( _ : Char) < _)  := reduceBinPred ``LT.lt 4 (. < .)
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_simproc [simp, seval] reduceLE  (( _ : Char) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_simproc [simp, seval] reduceGT  (( _ : Char) > _)  := reduceBinPred ``GT.gt 4 (. > .)
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_simproc [simp, seval] reduceGE  (( _ : Char) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_simproc [simp, seval] reduceEq  (( _ : Char) = _)  := reduceBinPred ``Eq 3 (. = .)
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_simproc [simp, seval] reduceNe  (( _ : Char) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceBEq  (( _ : Char) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceBNe  (( _ : Char) != _)  := reduceBoolPred ``bne 4 (. != .)

set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
/--
Returns `.done` for Char values.

These values should not be unfolded in the symbolic evaluator.

In regular `simp`, the nested raw literal should be prevented from being converted into an
`OfNat.ofNat` application.
-/
-- TODO: cleanup
builtin_dsimproc ↓ [simp, seval] isValue (Char.ofNat _ ) := fun e => do
  unless (← fromExpr? e).isSome do return .continue
  return .done e

set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceOfNatAux (Char.ofNatAux _ _) := fun e => do
  let_expr Char.ofNatAux n _ ← e | return .continue
  let some n ← Nat.fromExpr? n | return .continue
  return .done <| toExpr (Char.ofNat n)

set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
builtin_dsimproc [simp, seval] reduceDefault ((default : Char)) := fun e => do
  let_expr default _ _ ← e | return .continue
  return .done <| toExpr (default : Char)

set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
/-- Simplifies `Nat.digitChar n = c` to `False` when `c` is a concrete character
not in the range of `digitChar` (i.e., not one of `'0'`-`'9'`, `'a'`-`'f'`, `'*'`). -/
builtin_simproc [simp, seval] Nat.reduceDigitCharEq (Nat.digitChar _ = _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let lhs := e.appFn!.appArg!
  let rhs := e.appArg!
  unless lhs.isAppOfArity ``Nat.digitChar 1 do return .continue
  let some c ← fromExpr? rhs | return .continue
  let digitChars : Array Char :=
    #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', '*']
  if digitChars.contains c then return .continue
  let n := lhs.appArg!
  let neProof := mkApp3 (mkConst (Name.mkStr2 "Nat" "digitChar_ne")) n rhs eagerReflBoolTrue
  let proof := mkApp2 (mkConst ``eq_false) e neProof
  return .done { expr := mkConst ``False, proof? := proof }

set_option linter.coreInternal.internalModule false in -- User-facing builtin simprocs are fine
/-- Simplifies `c = Nat.digitChar n` to `False` when `c` is a concrete character
not in the range of `digitChar` (i.e., not one of `'0'`-`'9'`, `'a'`-`'f'`, `'*'`). -/
builtin_simproc [simp, seval] Nat.reduceEqDigitChar (_ = Nat.digitChar _) := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let charExpr := e.appFn!.appArg!
  let digitCharExpr := e.appArg!
  unless digitCharExpr.isAppOfArity ``Nat.digitChar 1 do return .continue
  let some c ← fromExpr? charExpr | return .continue
  let digitChars : Array Char :=
    #['0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', '*']
  if digitChars.contains c then return .continue
  let n := digitCharExpr.appArg!
  let neProof := mkApp3 (mkConst (Name.mkStr2 "Nat" "digitChar_ne")) n charExpr eagerReflBoolTrue
  let neSymProof := mkApp4 (mkConst ``Ne.symm [.succ .zero]) (mkConst ``Char) digitCharExpr charExpr neProof
  let proof := mkApp2 (mkConst ``eq_false) e neSymProof
  return .done { expr := mkConst ``False, proof? := proof }

end Char
