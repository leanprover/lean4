/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes
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
    unless decl.type == fnDecl.type do
      throwError "invalid function '{fnName}' type mismatch"
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
