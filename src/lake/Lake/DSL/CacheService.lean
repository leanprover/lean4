/-
Copyright (c) 2026 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.DSL.Syntax
public import Lake.Config.Cache

/-! # DSL for Cache Services
Macro for declaring a cache service.
-/

open Lean Parser Elab Command

namespace Lake.DSL

@[builtin_command_elab cacheServiceCommand]
def elabCacheServiceCommand : CommandElab := fun stx => do
  let `(cacheServiceCommand|$(doc?)? $(attrs?)? cache_service%$kw $(nameStx?)? := $defn $[$wds?:whereDecls]?) := stx
    | throwErrorAt stx "ill-formed cache_service declaration"
  withRef kw do
  let id ← mkConfigDeclIdent nameStx?
  let defn ←
    if let some nameStx := nameStx? then
      let name := expandIdentOrStrAsStrLit nameStx
      withRef nameStx ``(CacheService.withNameD $defn (CacheServiceName.ofString $name))
    else pure defn
  let attr ← `(Term.attrInstance| «cache_service»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let cmd ← `(
    $[$doc?:docComment]? @[$attrs,*] def $id : CacheService :=
      $defn
    $[$wds?:whereDecls]?
  )
  withMacroExpansion stx cmd <| elabCommand cmd
