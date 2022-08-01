/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Attributes

namespace Lean

private def isValidCppId (id : String) : Bool :=
  let first := id.get 0;
  first.isAlpha  && (id.toSubstring.drop 1).all (fun c => c.isAlpha || c.isDigit || c == '_')

private def isValidCppName : Name → Bool
  | .str .anonymous s => isValidCppId s
  | .str p s          => isValidCppId s && isValidCppName p
  | _                 => false

builtin_initialize exportAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `export,
    descr := "name to be used by code generators",
    getParam := fun _ stx => do
      let exportName ← Attribute.Builtin.getId stx
      unless isValidCppName exportName do
        throwError "invalid 'export' function name, is not a valid C++ identifier"
      return exportName
  }

@[export lean_get_export_name_for]
def getExportNameFor? (env : Environment) (n : Name) : Option Name :=
  exportAttr.getParam? env n

def isExport (env : Environment) (n : Name) : Bool :=
  -- The main function morally is an exported function as well. In particular,
  -- it should not participate in borrow inference.
  (getExportNameFor? env n).isSome || n == `main

end Lean
