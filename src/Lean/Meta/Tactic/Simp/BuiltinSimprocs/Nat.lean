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
  return some n

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Nat → Nat → Nat) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some n ← fromExpr? e.appFn!.appArg! | return none
  let some m ← fromExpr? e.appArg! | return none
  return some (.done { expr := mkNatLit (op n m) })

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some n ← fromExpr? e.appFn!.appArg! | return none
  let some m ← fromExpr? e.appArg! | return none
  let d ← mkDecide e
  if op n m then
    return some (.done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] })
  else
    return some (.done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] })

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

end Nat
