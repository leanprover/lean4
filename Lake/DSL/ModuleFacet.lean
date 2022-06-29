/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.DeclUtil
import Lake.Config.ModuleFacetConfig

namespace Lake.DSL
open Lean Parser Command

syntax moduleFacetDeclSpec :=
  ident Term.typeSpec declValSimple

scoped macro (name := moduleFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"module_facet " spec:moduleFacetDeclSpec : command => do
  match spec with
  | `(moduleFacetDeclSpec| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← `(Term.attrInstance| moduleFacet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let axm := mkIdentFrom id <| ``Lake.ModuleData ++ id.getId
    `(module_data $id : ActiveBuildTarget $ty
      $[$doc?]? @[$attrs,*] def $id : ModuleFacetConfig := {
        facet := $(WfName.quoteFrom id (WfName.ofName id.getId))
        resultType := $ty
        build := $defn
        data_eq_target := $axm
      })
  | stx => Macro.throwErrorAt stx "ill-formed module facet declaration"
