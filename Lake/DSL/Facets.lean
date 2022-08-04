/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.DeclUtil
import Lake.Config.FacetConfig
import Lake.Config.TargetConfig
import Lake.Build.Index

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
    let name := Name.quoteFrom id id.getId
    `(module_data $id : BuildJob $ty
      $[$doc?]? @[$attrs,*] def $id : ModuleFacetDecl := {
        name := $name
        config := Lake.mkFacetJobConfig $defn
      } $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed module facet declaration"

scoped macro (name := packageFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"package_facet " sig:simpleDeclSig : command => do
  match sig with
  | `(simpleDeclSig| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| packageFacet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    `(package_data $id : BuildJob $ty
      $[$doc?]? @[$attrs,*] def $id : PackageFacetDecl := {
        name := $name
        config := Lake.mkFacetJobConfig $defn
      } $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed package facet declaration"

scoped macro (name := libraryFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"library_facet " sig:simpleDeclSig : command => do
  match sig with
  | `(simpleDeclSig| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| libraryFacet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    `(library_data $id : BuildJob $ty
      $[$doc?]? @[$attrs,*] def $id : LibraryFacetDecl := {
        name := $name
        config := Lake.mkFacetJobConfig $defn
      } $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed library facet declaration"

scoped macro (name := targetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"target " sig:simpleDeclSig : command => do
  match sig with
  | `(simpleDeclSig| $id:ident : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| target)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    let pkgName := mkIdentFrom id `_package.name
    `(family_def $id : CustomData ($pkgName, $name) := BuildJob $ty
      $[$doc?]? @[$attrs,*] def $id : TargetDecl := {
        pkg := $pkgName
        name := $name
        config := Lake.mkTargetJobConfig $defn
      }  $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed target declaration"

--------------------------------------------------------------------------------
/-! # External Library Target -/
--------------------------------------------------------------------------------

syntax externLibDeclSpec :=
  ident declValSimple

/--
Define a new external library target for the package. Has one form:

```lean
extern_lib «target-name» := /- build function term -/
```

The term should be of type `Package → IndexBuildM (BuildJob FilePath)` and
build the external library's **static** library.
-/
scoped macro (name := externLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"extern_lib " spec:externLibDeclSpec : command => do
  match spec with
  | `(externLibDeclSpec| $id:ident := $defn $[$wds?]?) =>
    let attr ← `(Term.attrInstance| externLib)
    let attrs := #[attr] ++ expandAttrs attrs?
    let pkgName := mkIdentFrom id `_package.name
    let targetId := mkIdentFrom id <| id.getId.modifyBase (· ++ `static)
    let name := Name.quoteFrom id id.getId
    `(target $targetId : FilePath := $defn $[$wds?]?
      $[$doc?:docComment]? @[$attrs,*] def $id : ExternLibDecl := {
        pkg := $pkgName
        name := $name
        config := {getJob := ofFamily}
      })
  | stx => Macro.throwErrorAt stx "ill-formed external library declaration"
