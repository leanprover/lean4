/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Config.Package
import Lake.DSL.Attributes
import Lake.DSL.DeclUtil

namespace Lake.DSL
open Lean Parser Command

syntax scriptDeclSpec :=
  ident (ppSpace simpleBinder)? (declValSimple <|> declValDo)

scoped syntax (name := scriptDecl)
(docComment)? "script " scriptDeclSpec : command

@[macro scriptDecl]
def expandScriptDecl : Macro
| `($[$doc?]? script $id:ident $[$args?]? do $seq $[$wds?]?) => do
  `($[$doc?]? script $id:ident $[$args?]? := do $seq $[$wds?]?)
| `($[$doc?]? script $id:ident $[$args?]? := $defn $[$wds?]?) => do
  let args ← expandOptSimpleBinder args?
  `($[$doc?]? @[«script»] def $id : ScriptFn := fun $args => $defn $[$wds?]?)
| stx => Macro.throwErrorAt stx "ill-formed script declaration"
