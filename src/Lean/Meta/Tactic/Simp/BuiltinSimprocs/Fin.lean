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

def fromExpr? (e : Expr) : SimpM (Option Value) := OptionT.run do
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  let type ← whnf e.appFn!.appFn!.appArg!
  guard (type.isAppOfArity ``Fin 1)
  let size ← Nat.fromExpr? type.appArg!
  guard (size > 0)
  let value ← Nat.fromExpr? e.appFn!.appArg!
  let value := value % size
  return { size, value, ofNatFn := e.appFn!.appFn! }

def Value.toExpr (v : Value) : Expr :=
  let vExpr := mkRawNatLit v.value
  mkApp2 v.ofNatFn vExpr (mkApp2 (mkConst ``Fin.instOfNat) (Lean.toExpr (v.size - 1)) vExpr)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Nat → Nat → Nat) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  unless v₁.size == v₂.size do return .continue
  let v := { v₁ with value := op v₁.value v₂.value % v₁.size }
  return .done { expr := v.toExpr }

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  let d ← mkDecide e
  if op v₁.value v₂.value then
    return .done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
  else
    return .done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }

/-
The following code assumes users did not override the `Fin n` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_simproc [simp, seval] reduceAdd ((_ + _ : Fin _)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc [simp, seval] reduceMul ((_ * _ : Fin _)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc [simp, seval] reduceSub ((_ - _ : Fin _)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc [simp, seval] reduceDiv ((_ / _ : Fin _)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc [simp, seval] reduceMod ((_ % _ : Fin _)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc [simp, seval] reduceLT  (( _ : Fin _) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Fin _) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Fin _) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Fin _) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

/-- Return `.done` for Fin values. We don't want to unfold in the symbolic evaluator. -/
builtin_simproc [seval] isValue ((OfNat.ofNat _ : Fin _)) := fun e => do
  unless e.isAppOfArity ``OfNat.ofNat 3 do return .continue
  return .done { expr := e }

end Fin
