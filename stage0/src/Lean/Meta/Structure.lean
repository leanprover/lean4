/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura

Additional helper methods that require `MetaM` infrastructure.
-/
import Lean.Structure
import Lean.Meta.AppBuilder

namespace Lean.Meta

def getStructureName (struct : Expr) : MetaM Name :=
  match struct.getAppFn with
  | Expr.const declName .. => do
    unless isStructure (← getEnv) declName do
      throwError "'{declName}' is not a structure"
    return declName
  | _ => throwError "expected structure"

end Lean.Meta
