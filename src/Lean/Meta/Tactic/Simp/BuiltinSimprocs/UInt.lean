/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat

open Lean Meta Simp

macro "declare_uint_simprocs" typeName:ident : command =>
let ofNat := typeName.getId ++ `ofNat
let fromExpr := mkIdent `fromExpr
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

def $toExpr (v : Value) : Expr :=
  let vExpr := mkRawNatLit v.value.val
  mkApp2 v.ofNatFn vExpr (mkApp (mkConst $(quote (typeName.getId ++ `instOfNat))) vExpr)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : $typeName → $typeName → $typeName) (e : Expr) : OptionT SimpM Step := do
  guard (e.isAppOfArity declName arity)
  let n ← ($fromExpr e.appFn!.appArg!)
  let m ← ($fromExpr e.appArg!)
  let r := { n with value := op n.value m.value }
  return .done { expr := $toExpr r }

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : OptionT SimpM Step := do
  guard (e.isAppOfArity declName arity)
  let n ← ($fromExpr e.appFn!.appArg!)
  let m ← ($fromExpr e.appArg!)
  let d ← mkDecide e
  if op n.value m.value then
    return .done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] }
  else
    return .done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] }

builtin_simproc $(mkIdent `reduceAdd):ident ((_ + _ : $typeName)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc $(mkIdent `reduceMul):ident ((_ * _ : $typeName)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc $(mkIdent `reduceSub):ident ((_ - _ : $typeName)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc $(mkIdent `reduceDiv):ident ((_ / _ : $typeName)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc $(mkIdent `reduceMod):ident ((_ % _ : $typeName)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc $(mkIdent `reduceLT):ident  (( _ : $typeName) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc $(mkIdent `reduceLE):ident  (( _ : $typeName) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc $(mkIdent `reduceGT):ident  (( _ : $typeName) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc $(mkIdent `reduceGE):ident  (( _ : $typeName) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

/-- Return `.done` for UInt values. We don't want to unfold them when `ground := true`. -/
builtin_simproc isValue ((OfNat.ofNat _ : $typeName)) := fun e => OptionT.run do
  guard (← getContext).unfoldGround
  guard (e.isAppOfArity ``OfNat.ofNat 3)
  return .done { expr := e }

end $typeName
)

declare_uint_simprocs UInt8
declare_uint_simprocs UInt16
declare_uint_simprocs UInt32
declare_uint_simprocs UInt64
declare_uint_simprocs USize
