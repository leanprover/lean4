/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import init.lean.attributes

namespace Lean

private def isValidCppId (id : String) : Bool :=
let first := id.get 0 in
first.isAlpha  && (id.toSubstring.drop 1).all (λ c, c.isAlpha || c.isDigit || c == '_')

private def isValidCppName : Name → Bool
| (Name.mkString Name.anonymous s) := isValidCppId s
| (Name.mkString p s) := isValidCppId s && isValidCppName p
| _ := false

def mkExportAttr : IO (ParametricAttribute Name) :=
registerParametricAttribute `export "name to be used by code generators" $ λ _ _ stx,
  match attrParamSyntaxToIdentifier stx with
  | some exportName :=
    if isValidCppName exportName then Except.ok exportName
    else Except.error "invalid 'export' function name, is not a valid C++ identifier"
  | _ := Except.error "unexpected kind of argument"

@[init mkExportAttr]
constant exportAttr : ParametricAttribute Name := default _

@[export lean.get_export_name_for_core]
def getExportNameFor (env : Environment) (n : Name) : Option Name :=
exportAttr.getParam env n

def isExport (env : Environment) (n : Name) : Bool :=
(getExportNameFor env n).isSome

end Lean
