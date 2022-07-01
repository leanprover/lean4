/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.DeclUtil
import Lake.Config.ModuleFacetConfig

namespace Lake.DSL
open Lean Parser Command

scoped macro (name := moduleFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"module_facet " sig:simpleDeclSig : command => do
  match sig with
  | `(simpleDeclSig| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| moduleFacet)
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
