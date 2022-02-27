/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.LinearArith.Nat

namespace Lean.Meta.Linear

/-- Quick filter simpExpr? -/
private partial def isSimpExprTarget (e : Expr) : Bool :=
  let f := e.getAppFn
  if !f.isConst then
    false
  else
    let n := f.constName!
    n == ``HAdd.hAdd || n == ``HMul.hMul || n == ``HSub.hSub || n == ``Nat.succ

/-- Quick filter simpCnstr? -/
private partial def isSimpCnstrTarget (e : Expr) : Bool :=
  let f := e.getAppFn
  if !f.isConst then
    false
  else
    let n := f.constName!
    if n == ``Eq || n == ``LT.lt || n == ``LE.le || n == ``GT.gt || n == ``GE.ge then
      true
    else if n == ``Not && e.getAppNumArgs == 1 then
      isSimpCnstrTarget e.appArg!
    else
      false

private def parentIsTarget (parent? : Option Expr) : Bool :=
  match parent? with
  | none => false
  | some parent => isSimpExprTarget parent || isSimpCnstrTarget parent

def simp? (e : Expr) (parent? : Option Expr) : MetaM (Option (Expr × Expr)) := do
  -- TODO: add support for `Int` and arbitrary ordered comm rings
  if isSimpCnstrTarget e then
    Nat.simpCnstr? e
  else if isSimpExprTarget e && !parentIsTarget parent? then
    trace[Meta.Tactic.simp] "arith expr: {e}"
    Nat.simpExpr? e
  else
    return none

end Lean.Meta.Linear
