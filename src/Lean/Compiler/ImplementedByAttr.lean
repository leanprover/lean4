#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes
import Lean.MonadEnv

namespace Lean.Compiler

builtin_initialize implementedByAttr : ParametricAttribute Name ←
registerParametricAttribute `implementedBy "name of the Lean (probably unsafe) function that implements opaque constant" fun declName stx => do
  let decl ← getConstInfo declName
  match attrParamSyntaxToIdentifier stx with
  | some fnName =>
    let fnName ← resolveGlobalConstNoOverload fnName;
    let fnDecl ← getConstInfo fnName;
    if decl.type == fnDecl.type then pure fnName
    else throwError! "invalid function '{fnName}' type mismatch"
  | _ => throwError "expected identifier"

@[export lean_get_implemented_by]
def getImplementedBy (env : Environment) (declName : Name) : Option Name :=
implementedByAttr.getParam env declName

def setImplementedBy (env : Environment) (declName : Name) (impName : Name) : Except String Environment :=
implementedByAttr.setParam env declName impName

end Compiler

def setImplementedBy {m} [Monad m] [MonadEnv m] [MonadExceptOf Exception m] [Ref m] [AddErrorMessageContext m]
    (declName : Name) (impName : Name) : m Unit := do
let env ← getEnv
match Compiler.setImplementedBy env declName impName with
| Except.ok env   => setEnv env
| Except.error ex => throwError ex

end Lean
