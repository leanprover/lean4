/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.DeclUtil
import Lake.Config.ModuleFacetConfig
import Lake.Config.PackageFacetConfig
import Lake.Config.TargetConfig

/-!
Macros for declaring custom facets and targets.
-/

namespace Lake.DSL
open Lean Parser Command

scoped macro (name := moduleFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"module_facet " sig:simpleDeclSig : command => do
  match sig with
  | `(simpleDeclSig| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| moduleFacet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let axm := mkIdentFrom id <| ``ModuleData ++ id.getId
    `(module_data $id : ActiveBuildTarget $ty
      $[$doc?]? @[$attrs,*] def $id : ModuleFacetConfig := {
        name := $(WfName.quoteFrom id (WfName.ofName id.getId))
        resultType := $ty
        build := $defn
        data_eq_target := $axm
      })
  | stx => Macro.throwErrorAt stx "ill-formed module facet declaration"

scoped macro (name := packageFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"package_facet " sig:simpleDeclSig : command => do
  match sig with
  | `(simpleDeclSig| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| packageFacet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let axm := mkIdentFrom id <| ``PackageData ++ id.getId
    `(package_data $id : ActiveBuildTarget $ty
      $[$doc?]? @[$attrs,*] def $id : PackageFacetConfig := {
        name := $(WfName.quoteFrom id (WfName.ofName id.getId))
        resultType := $ty
        build := $defn
        data_eq_target := $axm
      })
  | stx => Macro.throwErrorAt stx "ill-formed package facet declaration"

scoped macro (name := targetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"target " sig:simpleDeclSig : command => do
  match sig with
  | `(simpleDeclSig| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| target)
    let attrs := #[attr] ++ expandAttrs attrs?
    let axm := mkIdentFrom id <| ``CustomData ++ id.getId
    `(custom_data $id : ActiveBuildTarget $ty
      $[$doc?]? @[$attrs,*] def $id : TargetConfig := {
        name := $(WfName.quoteFrom id (WfName.ofName id.getId))
        resultType := $ty
        target := $defn
        data_eq_target := $axm
      })
  | stx => Macro.throwErrorAt stx "ill-formed target declaration"
