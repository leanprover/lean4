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

def $fromExpr (e : Expr) : SimpM (Option Value) := do
  unless e.isAppOfArity ``OfNat.ofNat 3 do return none
  let type ← whnf e.appFn!.appFn!.appArg!
  unless type.isConstOf $(quote typeName.getId) do return none
  let some value ← Nat.fromExpr? e.appFn!.appArg! | return none
  let value := $(mkIdent ofNat) value
  return some { value, ofNatFn := e.appFn!.appFn! }

def $toExpr (v : Value) : Expr :=
  let vExpr := mkRawNatLit v.value.val
  mkApp2 v.ofNatFn vExpr (mkApp (mkConst $(quote (typeName.getId ++ `ofNatInst))) vExpr)

@[inline] def reduceBin (declName : Name) (arity : Nat) (op : $typeName → $typeName → $typeName) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some n ← ($fromExpr e.appFn!.appArg!) | return none
  let some m ← ($fromExpr e.appArg!) | return none
  let r := { n with value := op n.value m.value }
  return some (.done { expr := $toExpr r })

@[inline] def reduceBinPred (declName : Name) (arity : Nat) (op : $typeName → $typeName → Bool) (e : Expr) : SimpM (Option Step) := do
  unless e.isAppOfArity declName arity do return none
  let some n ← ($fromExpr e.appFn!.appArg!) | return none
  let some m ← ($fromExpr e.appArg!) | return none
  let d ← mkDecide e
  if op n.value m.value then
    return some (.done { expr := mkConst ``True, proof? := mkAppN (mkConst ``eq_true_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``true))] })
  else
    return some (.done { expr := mkConst ``False, proof? := mkAppN (mkConst ``eq_false_of_decide) #[e, d.appArg!, (← mkEqRefl (mkConst ``false))] })

builtin_simproc $(mkIdent `reduceAdd):ident ((_ + _ : $typeName)) := reduceBin ``HAdd.hAdd 6 (· + ·)
builtin_simproc $(mkIdent `reduceMul):ident ((_ * _ : $typeName)) := reduceBin ``HMul.hMul 6 (· * ·)
builtin_simproc $(mkIdent `reduceSub):ident ((_ - _ : $typeName)) := reduceBin ``HSub.hSub 6 (· - ·)
builtin_simproc $(mkIdent `reduceDiv):ident ((_ / _ : $typeName)) := reduceBin ``HDiv.hDiv 6 (· / ·)
builtin_simproc $(mkIdent `reduceMod):ident ((_ % _ : $typeName)) := reduceBin ``HMod.hMod 6 (· % ·)

builtin_simproc $(mkIdent `reduceLT):ident  (( _ : $typeName) < _)  := reduceBinPred ``LT.lt 4 (. < .)
builtin_simproc $(mkIdent `reduceLE):ident  (( _ : $typeName) ≤ _)  := reduceBinPred ``LE.le 4 (. ≤ .)
builtin_simproc $(mkIdent `reduceGT):ident  (( _ : $typeName) > _)  := reduceBinPred ``GT.gt 4 (. > .)
builtin_simproc $(mkIdent `reduceGE):ident  (( _ : $typeName) ≥ _)  := reduceBinPred ``GE.ge 4 (. ≥ .)

end $typeName
)

declare_uint_simprocs UInt8
declare_uint_simprocs UInt16
declare_uint_simprocs UInt32
declare_uint_simprocs UInt64
declare_uint_simprocs USize
