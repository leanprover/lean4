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
  let type := mkConst type
  let rec go (i : Nat) (atoms' : Array Expr) (xs : Array Expr) (args : Array Expr) : MetaM (Option (Expr × Expr)) := do
    if h : i < atoms.size then
      let atom := atoms[i]
      if atom.isFVar then
        go (i+1) (atoms'.push atom) xs args
      else
        withLocalDeclD (← mkFreshUserName `x) type fun x =>
          go (i+1) (atoms'.push x) (xs.push x) (args.push atom)
    else
      if xs.isEmpty then
        k atoms'
      else
        let some (r, p) ← k atoms' | return none
        let r := (← mkLambdaFVars xs r).beta args
        let p := mkAppN (← mkLambdaFVars xs p) args
        return some (r, p)
  go 0 #[] #[] #[]

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

def isDvdCnstr (e : Expr) : Bool :=
  e.isAppOfArity ``Dvd.dvd 4

end Lean.Meta.Linear
