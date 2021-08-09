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

def getFieldType (structType : Expr) (fieldName : Name) : MetaM Expr := do
  let structName ← getStructureName structType
  match findField? (← getEnv) structName fieldName with
  | some baseStructName =>
    match getPathToBaseStructure? (← getEnv) baseStructName structName with
    | none => throwError "failed to access field '{fieldName}' of structure '{structName}'"
    | some path =>
      match getProjFnForField? (← getEnv) baseStructName fieldName with
      | none => unreachable!
      | some projFn =>
        withLocalDeclD `s structType fun struct => do
          let mut struct := struct
          for toField in path do
            struct ← mkAppM toField #[struct]
          let fieldVal ← mkAppM projFn #[struct]
          let fieldType ← inferType fieldVal
          return fieldType
  | none => throwError "'{fieldName}' is not a field of structure '{structName}'"

end Lean.Meta
