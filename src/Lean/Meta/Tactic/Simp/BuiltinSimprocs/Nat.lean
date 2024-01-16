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

@[inline] def reduceUnary (declName : Name) (arity : Nat) (op : Nat → Nat) (e : Expr) : OptionT SimpM Step := do
  guard (e.isAppOfArity declName arity)
  let n ← fromExpr? e.appArg!
  return .done { expr := mkNatLit (op n) }

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Nat → Nat → Nat) (e : Expr) : OptionT SimpM Step := do
  guard (e.isAppOfArity declName arity)
  let n ← fromExpr? e.appFn!.appArg!
  let m ← fromExpr? e.appArg!
  return .done { expr := mkNatLit (op n m) }

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : OptionT SimpM Step := do
  guard (e.isAppOfArity declName arity)
  let n ← fromExpr? e.appFn!.appArg!
  let m ← fromExpr? e.appArg!
  let d ← mkDecide e
  if op n m then
    return .done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
  else
    return .done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }

builtin_simproc reduceSucc (Nat.succ _) := reduceUnary ``Nat.succ 1 (· + 1)

/-
The following code assumes users did not override the `Nat` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_simproc reduceAdd ((_ + _ : Nat)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc reduceMul ((_ * _ : Nat)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc reduceSub ((_ - _ : Nat)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc reduceDiv ((_ / _ : Nat)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc reduceMod ((_ % _ : Nat)) := reduceBin ``HMod.hMod 6 (· % ·)
builtin_simproc reducePow ((_ ^ _ : Nat)) := reduceBin ``HPow.hPow 6 (· ^ ·)
builtin_simproc reduceGcd (gcd _ _)       := reduceBin ``gcd 2 gcd

builtin_simproc reduceLT  (( _ : Nat) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc reduceLE  (( _ : Nat) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc reduceGT  (( _ : Nat) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc reduceGE  (( _ : Nat) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

/-- Return `.done` for Nat values. We don't want to unfold them when `ground := true`. -/
builtin_simproc isValue ((OfNat.ofNat _ : Nat)) := fun e => OptionT.run do
  guard (← getContext).unfoldGround
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  return .done { expr := e }

end Nat
