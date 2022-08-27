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
  declName == ``Coe.coe || declName == ``CoeTC.coe || declName == ``CoeHead.coe ||
  declName == ``CoeTail.coe || declName == ``CoeHTCT.coe || declName == ``CoeDep.coe ||
  declName == ``CoeT.coe || declName == ``CoeFun.coe || declName == ``CoeSort.coe ||
  declName == ``Lean.Internal.liftCoeM || declName == ``Lean.Internal.coeM

/-- Expand coercions occurring in `e` -/
partial def expandCoe (e : Expr) : MetaM Expr :=
  withReducibleAndInstances do
    transform e fun e => do
      let f := e.getAppFn
      if f.isConst then
        let declName := f.constName!
        if isCoeDecl declName then
          if let some e ← unfoldDefinition? e then
            return .visit e.headBeta
      return .continue

end Lean.Meta
