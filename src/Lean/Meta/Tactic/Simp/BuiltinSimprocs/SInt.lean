/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Markus Himmel
-/
prelude
import Lean.Meta.LitValues
import Init.Data.SInt.Lemmas
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Int

open Lean Meta Simp

macro "declare_sint_simprocs" typeName:ident : command =>
let ofNat := typeName.getId ++ `ofNat
let ofInt := typeName.getId ++ `ofInt
let ofIntLE := mkIdent (typeName.getId ++ `ofIntLE)
let toInt := mkIdent (typeName.getId ++ `toInt)
let toNatClampNeg := mkIdent (typeName.getId ++ `toNatClampNeg)
let fromExpr := mkIdent `fromExpr
`(
namespace $typeName

def $fromExpr (e : Expr) : SimpM (Option $typeName) := do
  if let some (n, _) ← getOfNatValue? e $(quote typeName.getId) then
    return some ($(mkIdent ofNat) n)
  let_expr Neg.neg _ _ a ← e | return none
  let some (n, _) ← getOfNatValue? a $(quote typeName.getId) | return none
  return some ($(mkIdent ofInt) (- n))

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : $typeName → $typeName → $typeName) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  evalPropStep e (op n m)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM DStep := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done <| toExpr (op n m)

builtin_dsimproc [simp, seval] reduceNeg ((- _ : $typeName)) := fun e => do
  let_expr Neg.neg _ _ arg ← e | return .continue
  if arg.isAppOfArity ``OfNat.ofNat 3 then
    -- We return .done to ensure `Neg.neg` is not unfolded even when `ground := true`.
    return .done e
  else
    let some v ← ($fromExpr arg) | return .continue
    return .done <| toExpr (- v)

builtin_dsimproc [simp, seval] $(mkIdent `reduceAdd):ident ((_ + _ : $typeName)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceMul):ident ((_ * _ : $typeName)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceSub):ident ((_ - _ : $typeName)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceDiv):ident ((_ / _ : $typeName)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_dsimproc [simp, seval] $(mkIdent `reduceMod):ident ((_ % _ : $typeName)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc [simp, seval] $(mkIdent `reduceLT):ident  (( _ : $typeName) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] $(mkIdent `reduceLE):ident  (( _ : $typeName) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] $(mkIdent `reduceGT):ident  (( _ : $typeName) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] $(mkIdent `reduceGE):ident  (( _ : $typeName) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : $typeName) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : $typeName) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_dsimproc [simp, seval] reduceBEq  (( _ : $typeName) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_dsimproc [simp, seval] reduceBNe  (( _ : $typeName) != _)  := reduceBoolPred ``bne 4 (. != .)

builtin_dsimproc [simp, seval] $(mkIdent `reduceOfIntLE):ident ($ofIntLE _ _ _) := fun e => do
  unless e.isAppOfArity $(quote ofIntLE.getId) 3 do return .continue
  let some value ← Int.fromExpr? e.appFn!.appFn!.appArg! | return .continue
  let value := $(mkIdent ofInt) value
  return .done <| toExpr value

builtin_dsimproc [simp, seval] $(mkIdent `reduceOfNat):ident ($(mkIdent ofNat) _) := fun e => do
  unless e.isAppOfArity $(quote ofNat) 1 do return .continue
  let some value ← Nat.fromExpr? e.appArg! | return .continue
  let value := $(mkIdent ofNat) value
  return .done <| toExpr value

builtin_dsimproc [simp, seval] $(mkIdent `reduceOfInt):ident ($(mkIdent ofInt) _) := fun e => do
  unless e.isAppOfArity $(quote ofInt) 1 do return .continue
  let some value ← Int.fromExpr? e.appArg! | return .continue
  let value := $(mkIdent ofInt) value
  return .done <| toExpr value

builtin_dsimproc [simp, seval] $(mkIdent `reduceToInt):ident ($toInt _) := fun e => do
  unless e.isAppOfArity $(quote toInt.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toInt v
  return .done <| toExpr n

builtin_dsimproc [simp, seval] $(mkIdent `reduceToNatClampNeg):ident ($toNatClampNeg _) := fun e => do
  unless e.isAppOfArity $(quote toNatClampNeg.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toNatClampNeg v
  return .done <| toExpr n

/-- Return `.done` for Int values. We don't want to unfold in the symbolic evaluator. -/
builtin_dsimproc [seval] isValue ((OfNat.ofNat _ : $typeName)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done e

end $typeName
)

declare_sint_simprocs Int8
declare_sint_simprocs Int16
declare_sint_simprocs Int32
declare_sint_simprocs Int64

/-
We do not use the normal simprocs for `ISize` since the result of most operations depend on an opaque value: `System.Platform.numBits`.
However, we do reduce natural literals using the fact this opaque value is at least `32`.
-/
namespace ISize

builtin_simproc [simp, seval] reduceToNatClampNeg (ISize.toNatClampNeg _) := fun e => do
  let_expr ISize.toNatClampNeg e ← e | return .continue
  if let some (n, _) ← getOfNatValue? e ``ISize then
    unless n < 2 ^ 31 do return .continue
    let e := toExpr n
    let p ← mkDecideProof (← mkLT e (mkNatLit (2 ^ 31)))
    let p := mkApp2 (mkConst ``ISize.toNatClampNeg_ofNat_of_lt) e p
    return .done { expr := e, proof? := p }

  let_expr Neg.neg _ _ a ← e | return .continue
  let some (n, _) ← getOfNatValue? a ``ISize | return .continue
  unless n ≤ 2 ^ 31 do return .continue
  let e := toExpr n
  let p ← mkDecideProof (← mkLE e (mkNatLit (2 ^ 31)))
  let p := mkApp2 (mkConst ``ISize.toNatClampNeg_neg_ofNat_of_le) e p
  return .done { expr := toExpr 0, proof? := p }

builtin_simproc [simp, seval] reduceToInt (ISize.toInt _) := fun e => do
  let_expr ISize.toInt e ← e | return .continue
  if let some (n, _) ← getOfNatValue? e ``ISize then
    unless n < 2 ^ 31 do return .continue
    let e := toExpr n
    let p ← mkDecideProof (← mkLT e (mkNatLit (2 ^ 31)))
    let p := mkApp2 (mkConst ``ISize.toInt_ofNat_of_lt) e p
    return .done { expr := toExpr (n : Int), proof? := p }

  let_expr Neg.neg _ _ a ← e | return .continue
  let some (n, _) ← getOfNatValue? a ``ISize | return .continue
  unless n ≤ 2 ^ 31 do return .continue
  let e := toExpr n
  let p ← mkDecideProof (← mkLE e (mkNatLit (2 ^ 31)))
  let p := mkApp2 (mkConst ``ISize.toInt_neg_ofNat_of_le) e p
  return .done { expr := toExpr (-n : Int), proof? := p }
