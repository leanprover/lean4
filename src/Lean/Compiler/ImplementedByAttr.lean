/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean
namespace Compiler

def mkImplementedByAttr : IO (ParametricAttribute Name) :=
registerParametricAttribute `implementedBy "name of the Lean (probably unsafe) function that implements opaque constant" fun declName stx => do
  decl ← Core.getConstInfo declName;
  match attrParamSyntaxToIdentifier stx with
  | some fnName => do
    fnDecl ← Core.getConstInfo fnName;
    if decl.type == fnDecl.type then pure fnName
    else Core.throwError ("invalid function '" ++ fnName ++ "' type mismatch")
  | _ => Core.throwError "expected identifier"

@[init mkImplementedByAttr]
constant implementedByAttr : ParametricAttribute Name := arbitrary _

@[export lean_get_implemented_by]
def getImplementedBy (env : Environment) (n : Name) : Option Name :=
implementedByAttr.getParam env n

end Compiler
end Lean
