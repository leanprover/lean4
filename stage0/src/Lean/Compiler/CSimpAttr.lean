/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.ScopedEnvExtension
import Lean.Util.Recognizers
import Lean.Util.ReplaceExpr

namespace Lean.Compiler
namespace CSimp

structure Entry where
  fromDeclName : Name
  toDeclName   : Name
  deriving Inhabited

abbrev State := SMap Name Name

builtin_initialize ext : SimpleScopedEnvExtension Entry State ←
  registerSimpleScopedEnvExtension {
    name           := `csimp
    initial        := {}
    addEntry       := fun s { fromDeclName, toDeclName } => s.insert fromDeclName toDeclName
    finalizeImport := fun s => s.switch
  }

private def isConstantReplacement? (declName : Name) : CoreM (Option Entry) := do
  let info ← getConstInfo declName
  match info.type.eq? with
  | some (_, Expr.const fromDeclName us .., Expr.const toDeclName vs ..) =>
    if us == vs then
      return some { fromDeclName, toDeclName }
    else
      return none
  | _ => return none

def add (declName : Name) (kind : AttributeKind) : CoreM Unit := do
  if let some entry ← isConstantReplacement? declName then
    ext.add entry kind
  else
    throwError "invalid 'csimp' theorem, only constant replacement theorems (e.g., `@f = @g`) are currently supported."

builtin_initialize
  registerBuiltinAttribute {
    name  := `csimp
    descr := "simplification theorem for the compiler"
    add   := fun declName stx attrKind => do
      Attribute.Builtin.ensureNoArgs stx
      discard <| add declName attrKind
  }

@[export lean_csimp_replace_constants]
def replaceConstants (env : Environment) (e : Expr) : Expr :=
  let map := ext.getState env
  e.replace fun e =>
    if e.isConst then
      match map.find? e.constName! with
      | some declNameNew => some (mkConst declNameNew e.constLevels!)
      | none => none
    else
      none

end CSimp
end Lean.Compiler
