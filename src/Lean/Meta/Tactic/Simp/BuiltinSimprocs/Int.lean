/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ToExpr
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

namespace Int
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option Int) := do
  let mut e := e
  let mut isNeg := false
  if e.isAppOfArity ``Neg.neg 3 then
    e := e.appArg!
    isNeg := true
  unless e.isAppOfArity ``OfNat.ofNat 3 do return none
  let type ← whnf e.appFn!.appFn!.appArg!
  unless type.isConstOf ``Int do return none
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return none
  let mut value : Int := value
  if isNeg then value := - value
  return some value

def toExpr (v : Int) : Expr :=
  let n := v.natAbs
  let r := mkRawNatLit n
  let e := mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst ``Int) r (mkApp (mkConst ``ofNatInst) r)
  if v < 0 then
    mkAppN (mkConst ``Neg.neg [levelZero]) #[mkConst ``Int, mkConst ``instNegInt, e]
  else
    e

@[inline] def reduceUnary (declName : Name) (arity : Nat) (op : Int → Int) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some n ← fromExpr? e.appArg! | return none
  return some (.done { expr := toExpr (op n) })

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Int → Int → Int) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some v₁ ← fromExpr? e.appFn!.appArg! | return none
  let some v₂ ← fromExpr? e.appArg! | return none
  return some (.done { expr := toExpr (op v₁ v₂) })

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Int → Int → Bool) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some v₁ ← fromExpr? e.appFn!.appArg! | return none
  let some v₂ ← fromExpr? e.appArg! | return none
  let d ← mkDecide e
  if op v₁ v₂ then
    return some (.done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] })
  else
    return some (.done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] })

/-
The following code assumes users did not override the `Int` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_simproc reduceNeg ((- _ : Int)) := fun e => do
  unless e.isAppOfArity ``Neg.neg 3 do return none
  let some v ← fromExpr? e.appArg! | return none
  unless v < 0 do return none
  return some (.done { expr := toExpr (- v) })

builtin_simproc reduceAdd ((_ + _ : Int)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc reduceMul ((_ * _ : Int)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc reduceSub ((_ - _ : Int)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc reduceDiv ((_ / _ : Int)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc reduceMod ((_ % _ : Int)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc reducePow ((_ : Int) ^ (_ : Nat)) := fun e => do
  unless e.isAppOfArity ``HPow.hPow 6 do return none
  let some v₁ ← fromExpr? e.appFn!.appArg! | return none
  let some v₂ ← Nat.fromExpr? e.appArg! | return none
  return some (.done { expr := toExpr (v₁ ^ v₂) })

builtin_simproc reduceAbs (natAbs _) := fun e => do
  unless e.isAppOfArity ``natAbs 1 do return none
  let some v ← fromExpr? e.appArg! | return none
  return some (.done { expr := mkNatLit (natAbs v) })

builtin_simproc reduceLT  (( _ : Int) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc reduceLE  (( _ : Int) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc reduceGT  (( _ : Int) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc reduceGE  (( _ : Int) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

end Int
