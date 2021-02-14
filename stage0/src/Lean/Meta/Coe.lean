/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.WHNF
import Lean.Meta.Transform

namespace Lean.Meta

/--
  Return true iff `declName` is one of the auxiliary definitions/projections
  used to implement coercions.
-/
def isCoeDecl (declName : Name) : Bool :=
  declName == ``coe  ||
  declName == ``coeB ||  declName == ``coeHead || declName == ``coeTail || declName == ``coeD ||
  declName == ``coeTC || declName == ``coeFun || declName == ``coeSort ||
  declName == ``Coe.coe || declName == ``CoeTC.coe || declName == ``CoeHead.coe ||
  declName == ``CoeTail.coe || declName == ``CoeHTCT.coe || declName == ``CoeDep.coe ||
  declName == ``CoeT.coe || declName == ``CoeFun.coe || declName == ``CoeSort.coe ||
  declName == ``liftCoeM || declName == ``coeM

/-- Expand coercions occurring in `e` -/
partial def expandCoe (e : Expr) : MetaM Expr :=
  withReducibleAndInstances do
    return (← transform e (pre := step))
where
  step (e : Expr) : MetaM TransformStep := do
    let f := e.getAppFn
    if !f.isConst then
      return TransformStep.visit e
    else
      let declName := f.constName!
      if isCoeDecl declName then
        match (← unfoldDefinition? e) with
        | none   => return TransformStep.visit e
        | some e => step e.headBeta
      else
        return TransformStep.visit e

end Lean.Meta
