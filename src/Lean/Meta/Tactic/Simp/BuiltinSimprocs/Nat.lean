/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Offset
import Lean.Meta.Tactic.Simp.Simproc

namespace Nat
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option Nat) := do
  let some n ← evalNat e |>.run | return none
  return n

@[inline] def reduceUnary (declName : Name) (arity : Nat) (op : Nat → Nat) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit (op n) }

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Nat → Nat → Nat) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done { expr := mkNatLit (op n m) }

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  let d ← mkDecide e
  if op n m then
    return .done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
  else
    return .done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }

builtin_simproc [simp, seval] reduceSucc (Nat.succ _) := reduceUnary ``Nat.succ 1 (· + 1)

/-
The following code assumes users did not override the `Nat` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_simproc [simp, seval] reduceAdd ((_ + _ : Nat)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc [simp, seval] reduceMul ((_ * _ : Nat)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc [simp, seval] reduceSub ((_ - _ : Nat)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc [simp, seval] reduceDiv ((_ / _ : Nat)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc [simp, seval] reduceMod ((_ % _ : Nat)) := reduceBin ``HMod.hMod 6 (· % ·)
builtin_simproc [simp, seval] reducePow ((_ ^ _ : Nat)) := reduceBin ``HPow.hPow 6 (· ^ ·)
builtin_simproc [simp, seval] reduceGcd (gcd _ _)       := reduceBin ``gcd 2 gcd

builtin_simproc [simp, seval] reduceLT  (( _ : Nat) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Nat) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Nat) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Nat) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

/-- Return `.done` for Nat values. We don't want to unfold in the symbolic evaluator. -/
builtin_simproc [seval] isValue ((OfNat.ofNat _ : Nat)) := fun e => do
  unless e.isAppOfArity ``OfNat.ofNat 3 do return .continue
  return .done { expr := e }

end Nat
