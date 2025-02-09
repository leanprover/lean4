/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Basic
import Lean.Expr

namespace Lean.Meta.Linear
/-
To prevent the kernel from accidentially reducing the atoms in the equation while typechecking,
we abstract over them.
-/
def withAbstractAtoms (atoms : Array Expr) (type : Name) (k : Array Expr → MetaM (Option (Expr × Expr))) :
    MetaM (Option (Expr × Expr)) := do
  let atoms := atoms
  let decls : Array (Name × (Array Expr → MetaM Expr)) ← atoms.mapM fun _ => do
    return ((← mkFreshUserName `x), fun _ => pure (mkConst type))
  withLocalDeclsD decls fun ctxt => do
    let some (r, p) ← k ctxt | return none
    let r := (← mkLambdaFVars ctxt r).beta atoms
    let p := mkAppN (← mkLambdaFVars ctxt p) atoms
    return some (r, p)

/-- Quick filter for linear terms. -/
def isLinearTerm (e : Expr) : Bool :=
  let f := e.getAppFn
  if !f.isConst then
    false
  else
    let n := f.constName!
    n == ``HAdd.hAdd || n == ``HMul.hMul || n == ``HSub.hSub || n == ``Neg.neg || n == ``Nat.succ
    || n == ``Add.add || n == ``Mul.mul || n == ``Sub.sub

/-- Quick filter for linear constraints. -/
partial def isLinearCnstr (e : Expr) : Bool :=
  let f := e.getAppFn
  if !f.isConst then
    false
  else
    let n := f.constName!
    if n == ``Eq || n == ``LT.lt || n == ``LE.le || n == ``GT.gt || n == ``GE.ge || n == ``Ne then
      true
    else if n == ``Not && e.getAppNumArgs == 1 then
      isLinearCnstr e.appArg!
    else
      false

end Lean.Meta.Linear
