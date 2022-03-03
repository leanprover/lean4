/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Expr

namespace Lean.Meta.Linear

/-- Quick filter for linear terms. -/
def isLinearTerm (e : Expr) : Bool :=
  let f := e.getAppFn
  if !f.isConst then
    false
  else
    let n := f.constName!
    n == ``HAdd.hAdd || n == ``HMul.hMul || n == ``HSub.hSub || n == ``Nat.succ

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
