/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes
import Lean.Declaration
import Lean.MonadEnv

namespace Lean.Compiler

builtin_initialize implementedByAttr : ParametricAttribute Name ← registerParametricAttribute {
  name := `implementedBy
  descr := "name of the Lean (probably unsafe) function that implements opaque constant"
  getParam := fun declName stx => do
    let decl ← getConstInfo declName
    let fnName ← Attribute.Builtin.getIdent stx
    let fnName ← resolveGlobalConstNoOverload fnName
    let fnDecl ← getConstInfo fnName
    unless decl.levelParams.length == fnDecl.levelParams.length do
      throwError "invalid 'implementedBy' argument '{fnName}', '{fnName}' has {fnDecl.levelParams.length} universe level parameter(s), but '{declName}' has {decl.levelParams.length}"
    let declType := decl.type
    let fnType := fnDecl.instantiateTypeLevelParams (decl.levelParams.map mkLevelParam)
    unless declType == fnType do
      throwError "invalid 'implementedBy' argument '{fnName}', '{fnName}' has type{indentExpr fnType}\nbut '{declName}' has type{indentExpr declType}"
    if decl.name == fnDecl.name then
      throwError "invalid 'implementedBy' argument '{fnName}', function cannot be implemented by itself"
    return fnName
}

@[export lean_get_implemented_by]
def getImplementedBy (env : Environment) (declName : Name) : Option Name :=
  implementedByAttr.getParam env declName

def setImplementedBy (env : Environment) (declName : Name) (impName : Name) : Except String Environment :=
  implementedByAttr.setParam env declName impName

end Compiler

def setImplementedBy {m} [Monad m] [MonadEnv m] [MonadError m] (declName : Name) (impName : Name) : m Unit := do
  let env ← getEnv
  match Compiler.setImplementedBy env declName impName with
  | Except.ok env   => setEnv env
  | Except.error ex => throwError ex

end Lean
