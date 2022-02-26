/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.LinearArith.Nat

namespace Lean.Meta.Linear

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

def simpCnstr? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if isSimpCnstrTarget e then
    -- TODO: add support for `Int` and arbitrary ordered comm rings
    Nat.simpCnstr? e
  else
    return none

end Lean.Meta.Linear
