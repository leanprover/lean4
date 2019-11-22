/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Attributes

namespace Lean
namespace Compiler

def mkImplementedByAttr : IO (ParametricAttribute Name) :=
registerParametricAttribute `implementedBy "name of the Lean (probably unsafe) function that implements opaque constant" $ fun env declName stx =>
  match env.find declName with
  | none => Except.error "unknown declaration"
  | some decl =>
    match attrParamSyntaxToIdentifier stx with
    | some fnName =>
      match env.find fnName with
      | none => Except.error ("unknown function '" ++ toString fnName ++ "'")
      | some fnDecl =>
        if decl.type == fnDecl.type then Except.ok fnName
        else Except.error ("invalid function '" ++ toString fnName ++ "' type mismatch")
    | _ => Except.error "expected identifier"

@[init mkImplementedByAttr]
constant implementedByAttr : ParametricAttribute Name := arbitrary _

@[export lean_get_implemented_by]
def getImplementedBy (env : Environment) (n : Name) : Option Name :=
implementedByAttr.getParam env n

end Compiler
end Lean
