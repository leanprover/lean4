/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Prelude
import Lake.Config.Package  -- shake: keep (builtin macro output dependency)
import Lake.DSL.Attributes  -- shake: keep (builtin macro output dependency)
import Lake.DSL.Syntax

/-! # Script Declarations
DSL definitions to define a Lake script for a package.
-/

namespace Lake.DSL
open Lean Parser Command

@[builtin_macro scriptDecl]
def expandScriptDecl : Macro
| `($[$doc?]? $[$attrs?]? script%$kw $name $[$args?]? do $seq $[$wds?:whereDecls]?) => do
  `($[$doc?]? $[$attrs?]? script%$kw $name $[$args?]? := do $seq $[$wds?:whereDecls]?)
| `($[$doc?]? $[$attrs?]? script%$kw $name $[$args?]? := $defn $[$wds?:whereDecls]?) => withRef kw do
  let id := expandIdentOrStrAsIdent name
  let args ← expandOptSimpleBinder args?
  let attrs := #[← `(Term.attrInstance| «script»)] ++ expandAttrs attrs?
  `($[$doc?]? @[$attrs,*] def $id : ScriptFn := fun $args => $defn $[$wds?:whereDecls]?)
| stx => Macro.throwErrorAt stx "ill-formed script declaration"
