/-
Copyright (c) 2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.ToExpr
import Lean.Meta.LitValues
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

namespace Fin
open Lean Meta Simp

structure Value where
  n     : Nat
  value : Fin n
  deriving DecidableEq, Repr

def fromExpr? (e : Expr) : SimpM (Option Value) := do
  let some ⟨n, value⟩ ← getFinValue? e | return none
  return some { n, value }

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : {n : Nat} → Fin n → Fin n → Fin n) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  if h : v₁.n = v₂.n then
    let v := op v₁.value (h ▸ v₂.value)
    return .done <| toExpr v
  else
    return .continue

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  evalPropStep e (op v₁.value v₂.value)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : Nat → Nat → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some v₁ ← fromExpr? e.appFn!.appArg! | return .continue
  let some v₂ ← fromExpr? e.appArg! | return .continue
  return .done <| toExpr (op v₁.value v₂.value)

/-
The following code assumes users did not override the `Fin n` instances for the arithmetic operators.
If they do, they must disable the following `simprocs`.
-/

builtin_dsimproc [simp, seval] reduceAdd ((_ + _ : Fin _)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_dsimproc [simp, seval] reduceMul ((_ * _ : Fin _)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_dsimproc [simp, seval] reduceSub ((_ - _ : Fin _)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_dsimproc [simp, seval] reduceDiv ((_ / _ : Fin _)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_dsimproc [simp, seval] reduceMod ((_ % _ : Fin _)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc [simp, seval] reduceLT  (( _ : Fin _) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] reduceLE  (( _ : Fin _) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] reduceGT  (( _ : Fin _) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] reduceGE  (( _ : Fin _) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : Fin _) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : Fin _) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] reduceBEq  (( _ : Fin _) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] reduceBNe  (( _ : Fin _) != _)  := reduceBoolPred ``bne 4 (. != .)

/-- Simplification procedure for ensuring `Fin n` literals are normalized. -/
builtin_dsimproc [simp, seval] isValue ((OfNat.ofNat _ : Fin _)) := fun e => do
  let_expr OfNat.ofNat _ m _ ← e | return .continue
  let some ⟨n, v⟩ ← getFinValue? e | return .continue
  let some m ← getNatValue? m | return .continue
  if m < n then
    -- Design decision: should we return `.continue` instead of `.done` when simplifying.
    -- In the symbolic evaluator, we must return `.done`, otherwise it will unfold the `OfNat.ofNat`
    return .done e
  return .done <| toExpr v

builtin_dsimproc [simp, seval] reduceFinMk (Fin.mk _ _)  := fun e => do
  let_expr Fin.mk n v _ ← e | return .continue
  let some n ← evalNat n |>.run | return .continue
  let some v ← getNatValue? v | return .continue
  if h : n ≠ 0 then
    have : NeZero n := ⟨h⟩
    return .done <| toExpr (Fin.ofNat' n v)
  else
    return .continue

end Fin
