/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Simproc
import Lean.Meta.LitValues
import Lean.Meta.Offset
import Lean.Meta.Tactic.Simp.Simproc
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Util

namespace Nat
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option Nat) :=
  getNatValue? e

@[inline] def reduceUnary (declName : Name) (arity : Nat) (op : Nat → Nat) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Nat → Nat → Nat) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

builtin_dsimproc [simp, seval] reduceSucc (Nat.succ _) := reduceUnary ``Nat.succ 1 (· + 1)

/-
The following code assumes users did not override the `Nat` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_dsimproc [simp, seval] reduceAdd ((_ + _ : Nat)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_dsimproc [simp, seval] reduceMul ((_ * _ : Nat)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_dsimproc [simp, seval] reduceSub ((_ - _ : Nat)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_dsimproc [simp, seval] reduceDiv ((_ / _ : Nat)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_dsimproc [simp, seval] reduceMod ((_ % _ : Nat)) := reduceBin ``HMod.hMod 6 (· % ·)
builtin_dsimproc [simp, seval] reducePow ((_ ^ _ : Nat)) := reduceBin ``HPow.hPow 6 (· ^ ·)
builtin_dsimproc [simp, seval] reduceGcd (gcd _ _)       := reduceBin ``gcd 2 gcd

builtin_simproc [simp, seval] reduceLT  (( _ : Nat) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Nat) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Nat) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Nat) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : Nat) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : Nat) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] reduceBEq  (( _ : Nat) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] reduceBNe  (( _ : Nat) != _)  := reduceBoolPred ``bne 4 (. != .)

/-- Return `.done` for Nat values. We don't want to unfold in the symbolic evaluator. -/
builtin_dsimproc [seval] isValue ((OfNat.ofNat _ : Nat)) := fun e => do
  let_expr OfNat.ofNat _ _ _ ← e | return .continue
  return .done e

end Nat
