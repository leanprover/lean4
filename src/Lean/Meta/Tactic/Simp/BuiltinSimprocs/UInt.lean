/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

open Lean Meta Simp

macro "declare_uint_simprocs" typeName:ident : command =>
let ofNat := typeName.getId ++ `ofNat
let ofNatCore := mkIdent (typeName.getId ++ `ofNatCore)
let toNat := mkIdent (typeName.getId ++ `toNat)
let fromExpr := mkIdent `fromExpr
let toExprCore := mkIdent `toExprCore
let toExpr := mkIdent `toExpr
`(
namespace $typeName

structure Value where
  ofNatFn : Expr
  value   : $typeName

def $fromExpr (e : Expr) : OptionT SimpM Value := do
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  let type ← whnf e.appFn!.appFn!.appArg!
  guard (type.isConstOf $(quote typeName.getId))
  let value ← Nat.fromExpr? e.appFn!.appArg!
  let value := $(mkIdent ofNat) value
  return { value, ofNatFn := e.appFn!.appFn! }

def $toExprCore (v : $typeName) : Expr :=
  let vExpr := mkRawNatLit v.val
  mkApp3 (mkConst ``OfNat.ofNat [levelZero]) (mkConst $(quote typeName.getId)) vExpr (mkApp (mkConst $(quote (typeName.getId ++ `instOfNat))) vExpr)

def $toExpr (v : Value) : Expr :=
  let vExpr := mkRawNatLit v.value.val
  mkApp2 v.ofNatFn vExpr (mkApp (mkConst $(quote (typeName.getId ++ `instOfNat))) vExpr)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : $typeName → $typeName → $typeName) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  let r := { n with value := op n.value m.value }
  return .done { expr := $toExpr r }

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  evalPropStep e (op n.value m.value)

@[inline] def reduceBoolPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM Step := do
  unless e.isAppOfArity declName arity do return .continue
  let some n ← ($fromExpr e.appFn!.appArg!) | return .continue
  let some m ← ($fromExpr e.appArg!) | return .continue
  return .done { expr := Lean.toExpr (op n.value m.value) }

builtin_simproc [simp, seval] $(mkIdent `reduceAdd):ident ((_ + _ : $typeName)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc [simp, seval] $(mkIdent `reduceMul):ident ((_ * _ : $typeName)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc [simp, seval] $(mkIdent `reduceSub):ident ((_ - _ : $typeName)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc [simp, seval] $(mkIdent `reduceDiv):ident ((_ / _ : $typeName)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc [simp, seval] $(mkIdent `reduceMod):ident ((_ % _ : $typeName)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc [simp, seval] $(mkIdent `reduceLT):ident  (( _ : $typeName) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc [simp, seval] $(mkIdent `reduceLE):ident  (( _ : $typeName) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc [simp, seval] $(mkIdent `reduceGT):ident  (( _ : $typeName) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc [simp, seval] $(mkIdent `reduceGE):ident  (( _ : $typeName) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)
builtin_simproc [simp, seval] reduceEq  (( _ : $typeName) = _)  := reduceBinPred ``Eq 3 (. = .)
builtin_simproc [simp, seval] reduceNe  (( _ : $typeName) ≠ _)  := reduceBinPred ``Ne 3 (. ≠ .)
builtin_simproc [simp, seval] reduceBEq  (( _ : $typeName) == _)  := reduceBoolPred ``BEq.beq 4 (. == .)
builtin_simproc [simp, seval] reduceBNe  (( _ : $typeName) != _)  := reduceBoolPred ``bne 4 (. != .)

builtin_simproc [simp, seval] $(mkIdent `reduceOfNatCore):ident ($ofNatCore _ _) := fun e => do
  unless e.isAppOfArity $(quote ofNatCore.getId) 2 do return .continue
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return .continue
  let value := $(mkIdent ofNat) value
  let eNew := $toExprCore value
  return .done { expr := eNew }

builtin_simproc [simp, seval] $(mkIdent `reduceToNat):ident ($toNat _) := fun e => do
  unless e.isAppOfArity $(quote toNat.getId) 1 do return .continue
  let some v ← ($fromExpr e.appArg!) | return .continue
  let n := $toNat v.value
  return .done { expr := mkNatLit n }

/-- Return `.done` for UInt values. We don't want to unfold in the symbolic evaluator. -/
builtin_simproc [seval] isValue ((OfNat.ofNat _ : $typeName)) := fun e => do
  unless (e.isAppOfArity ``OfNat.ofNat 3) do return .continue
  return .done { expr := e }

end $typeName
)

declare_uint_simprocs UInt8
declare_uint_simprocs UInt16
declare_uint_simprocs UInt32
declare_uint_simprocs UInt64
declare_uint_simprocs USize
