/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.DSL.Syntax
import Lake.Config.Package
import Lake.DSL.Attributes
import Lake.DSL.Extensions
import Lake.DSL.DeclUtil

open Lean Parser Elab Command

namespace Lake.DSL

/-! # Package Declarations
DSL definitions for packages and hooks.
-/

@[builtin_command_elab packageCommand]
def elabPackageCommand : CommandElab := fun stx => do
  let `(packageCommand|$(doc?)? $(attrs?)? package%$kw $[$nameStx?]? $cfg) := stx
    | throwErrorAt stx "ill-formed package declaration"
  withRef kw do
  let configId : Ident ← `(pkgConfig)
  let id ← mkConfigDeclIdent nameStx?
  let origName := Name.quoteFrom id id.getId
  let ⟨idx, name⟩ := nameExt.getState (← getEnv)
  let name := match name with
    | .anonymous => origName
    | name => Name.quoteFrom id name
  let name := Syntax.mkCApp ``Name.num #[name, quote idx]
  let ty := Syntax.mkCApp ``PackageConfig #[name, origName]
  elabConfig ``PackageConfig configId ty cfg
  let attr ← `(Term.attrInstance| «package»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let id := mkIdentFrom id packageDeclName
  let decl ← `({name := $name, origName := $origName, config := $configId})
  let cmd ← `($[$doc?]? @[$attrs,*] abbrev $id : PackageDecl := $decl)
  withMacroExpansion stx cmd <| elabCommand cmd
  let nameId := mkIdentFrom id <| packageDeclName.str "name"
  elabCommand <| ← `(
    @[deprecated "Use `__name__` instead." (since := "2025-09-18")]
    abbrev $nameId := __name__
  )

@[builtin_macro postUpdateDecl]
def expandPostUpdateDecl : Macro := fun stx => do
  match stx with
  | `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? do $seq $[$wds?:whereDecls]?) =>
    `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? := do $seq $[$wds?:whereDecls]?)
  | `($[$doc?]? $[$attrs?]? post_update%$kw $[$pkg?]? := $defn $[$wds?:whereDecls]?) => withRef kw do
    let pkg ← expandOptSimpleBinder pkg?
    let attr ← `(Term.attrInstance| «post_update»)
    let attrs := #[attr] ++ expandAttrs attrs?
    `($[$doc?]? @[$attrs,*] def postUpdateHook : PostUpdateHookDecl :=
      {pkg := __name__, fn := fun $pkg => $defn} $[$wds?:whereDecls]?)
  | stx => Macro.throwErrorAt stx "ill-formed post_update declaration"
