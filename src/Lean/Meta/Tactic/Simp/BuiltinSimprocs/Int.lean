/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ToExpr
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

namespace Int
open Lean Meta Simp

def fromExpr? (e : Expr) : SimpM (Option Int) :=
  getIntValue? e

@[inline] def reduceUnary (declName : Name) (arity : Nat) (op : Int → Int) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : Int → Int → Int) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op v₁ v₂)

def reduceBinIntNatOp (name : Name) (op : Int → Nat → Int) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity name 2 do return .continue
  let some v₁ ← getIntValue? e.appFn!.appArg! | return .continue
  let some v₂ ← getNatValue? e.appArg! | return .continue
  return .done <| toExpr (op v₁ v₂)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Int → Int → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op v₁ v₂)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Int → Int → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← fromExpr? e.appFn!.appArg! | return .continue
  let some m ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op n m)

/-
The following code assumes users did not override the `Int` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_dsimproc [simp, seval] reduceNeg ((- _ : Int)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← fromExpr? arg | return .continue
    return .done <| toExpr (- v)

/-- Return `.done` for positive Int values. We don't want to unfold in the symbolic evaluator. -/
builtin_dsimproc [seval] isPosValue ((OfNat.ofNat _ : Int)) := fun e => do
  let_expr OfNat.ofNat _ _ _ ← e | return .continue
  return .done e

builtin_dsimproc [simp, seval] reduceAdd ((_ + _ : Int)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_dsimproc [simp, seval] reduceMul ((_ * _ : Int)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_dsimproc [simp, seval] reduceSub ((_ - _ : Int)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_dsimproc [simp, seval] reduceDiv ((_ / _ : Int)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_dsimproc [simp, seval] reduceMod ((_ % _ : Int)) := reduceBin ``HMod.hMod 6 (· % ·)
builtin_dsimproc [simp, seval] reduceTDiv (tdiv  _ _) := reduceBin ``Int.tdiv 2 Int.tdiv
builtin_dsimproc [simp, seval] reduceTMod (tmod  _ _) := reduceBin ``Int.tmod 2 Int.tmod
builtin_dsimproc [simp, seval] reduceFDiv (fdiv _ _) := reduceBin ``Int.fdiv 2 Int.fdiv
builtin_dsimproc [simp, seval] reduceFMod (fmod _ _) := reduceBin ``Int.fmod 2 Int.fmod
builtin_dsimproc [simp, seval] reduceBdiv (bdiv _ _) := reduceBinIntNatOp ``bdiv bdiv
builtin_dsimproc [simp, seval] reduceBmod (bmod _ _) := reduceBinIntNatOp ``bmod bmod

builtin_dsimproc [simp, seval] reducePow ((_ : Int) ^ (_ : Nat)) := fun e => do
  let_expr HPow.hPow _ _ _ _ a b ← e | return .continue
  let some v₁ ← fromExpr? a | return .continue
  let some v₂ ← Nat.fromExpr? b | return .continue
  unless (← checkExponent v₂) do return .continue
  return .done <| toExpr (v₁ ^ v₂)

builtin_simproc [simp, seval] reduceLT  (( _ : Int) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Int) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Int) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Int) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : Int) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : Int) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] reduceBEq  (( _ : Int) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] reduceBNe  (( _ : Int) != _)  := reduceBoolPred ``bne 4 (. != .)

@[inline] def reduceNatCore (declName : Name) (op : Int → Nat) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName 1 do return .continue
  let some v ← fromExpr? e.appArg! | return .continue
  return .done <| mkNatLit (op v)

builtin_dsimproc [simp, seval] reduceAbs (natAbs _) := reduceNatCore ``natAbs natAbs
builtin_dsimproc [simp, seval] reduceToNat (Int.toNat _) := reduceNatCore ``Int.toNat Int.toNat

builtin_dsimproc [simp, seval] reduceNegSucc (Int.negSucc _) := fun e => do
  let_expr Int.negSucc a ← e | return .continue
  let some a ← getNatValue? a | return .continue
  return .done <| toExpr (-(Int.ofNat a + 1))

builtin_dsimproc [simp, seval] reduceOfNat (Int.ofNat _) := fun e => do
  let_expr Int.ofNat a ← e | return .continue
  let some a ← getNatValue? a | return .continue
  return .done <| toExpr (Int.ofNat a)

builtin_simproc [simp, seval] reduceDvd ((_ : Int) ∣ _) := fun e => do
  let_expr Dvd.dvd _ i a b ← e | return .continue
  unless ← matchesInstance i (mkConst ``instDvd) do return .continue
  let some va ← fromExpr? a | return .continue
  let some vb ← fromExpr? b | return .continue
  if vb % va == 0 then
    return .done { expr := mkConst ``True, proof? := mkApp3 (mkConst ``Int.dvd_eq_true_of_mod_eq_zero) a b reflBoolTrue}
  else
    return .done { expr := mkConst ``False, proof? := mkApp3 (mkConst ``Int.dvd_eq_false_of_mod_ne_zero) a b reflBoolTrue}

end Int
