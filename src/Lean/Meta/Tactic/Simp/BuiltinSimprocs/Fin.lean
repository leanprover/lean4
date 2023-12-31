/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ToExpr
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

namespace Fin
open Lean Meta Simp

structure Value where
  ofNatFn   : Expr
  size      : Nat
  value     : Nat

def fromExpr? (e : Expr) : SimpM (Option Value) := do
  unless e.isAppOfArity ``OfNat.ofNat 3 do return none
  let type ← whnf e.appFn!.appFn!.appArg!
  unless type.isAppOfArity ``Fin 1 do return none
  let some size ← evalNat type.appArg! |>.run | return none
  unless size > 0 do return none
  let some value ← evalNat e.appFn!.appArg! |>.run | return none
  let value := value % size
  return some { size, value, ofNatFn := e.appFn!.appFn! }

def Value.toExpr (v : Value) : Expr :=
  let vExpr := mkRawNatLit v.value
  mkApp2 v.ofNatFn vExpr (mkApp2 (mkConst ``Fin.ofNatInst) (Lean.toExpr (v.size - 1)) vExpr)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Nat → Nat → Nat) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some v₁ ← fromExpr? e.appFn!.appArg! | return none
  let some v₂ ← fromExpr? e.appArg! | return none
  unless v₁.size == v₂.size do return none
  let v := { v₁ with value := op v₁.value v₂.value % v₁.size }
  return some (.done { expr := v.toExpr })

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some v₁ ← fromExpr? e.appFn!.appArg! | return none
  let some v₂ ← fromExpr? e.appArg! | return none
  let d ← mkDecide e
  if op v₁.value v₂.value then
    return some (.done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] })
  else
    return some (.done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] })

/-
The following code assumes users did not override the `Fin n` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_simproc reduceAdd ((_ + _ : Fin _)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc reduceMul ((_ * _ : Fin _)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc reduceSub ((_ - _ : Fin _)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc reduceDiv ((_ / _ : Fin _)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc reduceMod ((_ % _ : Fin _)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc reduceLT  (( _ : Fin _) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc reduceLE  (( _ : Fin _) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc reduceGT  (( _ : Fin _) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc reduceGE  (( _ : Fin _) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

end Fin
