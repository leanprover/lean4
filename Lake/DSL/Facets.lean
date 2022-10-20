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

syntax buildDeclSig :=
  ident (ppSpace simpleBinder)? Term.typeSpec declValSimple

/--
Define a new module facet. Has one form:

```lean
module_facet «facet-name» (mod : Module) : α :=
  /- build function term -/
```

The `mod` parameter (and its type specifier) is optional.
The term should be of type `IndexBuildM (BuildJob α)`.
-/
scoped macro (name := moduleFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"module_facet " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$mod?]? : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| module_facet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    let facetId := mkIdentFrom id <| id.getId.modifyBase (.str · "_modFacet")
    let mod ← expandOptSimpleBinder mod?
    `(module_data $id : BuildJob $ty
      $[$doc?:docComment]? @[$attrs,*] def $facetId : ModuleFacetDecl := {
        name := $name
        config := Lake.mkFacetJobConfig
          fun $mod => ($defn : IndexBuildM (BuildJob $ty))
      } $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed module facet declaration"

/--
Define a new package facet. Has one form:

```lean
package_facet «facet-name» (pkg : Package) : α :=
  /- build function term -/
```

The `pkg` parameter (and its type specifier) is optional.
The term should be of type `IndexBuildM (BuildJob α)`.
-/
scoped macro (name := packageFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"package_facet " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$pkg?]? : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| package_facet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    let facetId := mkIdentFrom id <| id.getId.modifyBase (.str · "_pkgFacet")
    let pkg ← expandOptSimpleBinder pkg?
    `(package_data $id : BuildJob $ty
      $[$doc?]? @[$attrs,*] def $facetId : PackageFacetDecl := {
        name := $name
        config := Lake.mkFacetJobConfig
          fun $pkg => ($defn : IndexBuildM (BuildJob $ty))
      } $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed package facet declaration"

/--
Define a new library facet. Has one form:

```lean
library_facet «facet-name» (lib : LeanLib) : α :=
  /- build function term -/
```

The `lib` parameter (and its type specifier) is optional.
The term should be of type `IndexBuildM (BuildJob α)`.
-/
scoped macro (name := libraryFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"library_facet " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$lib?]? : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| library_facet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    let facetId := mkIdentFrom id <| id.getId.modifyBase (.str · "_libFacet")
    let lib ← expandOptSimpleBinder lib?
    `(library_data $id : BuildJob $ty
      $[$doc?]? @[$attrs,*] def $facetId : LibraryFacetDecl := {
        name := $name
        config := Lake.mkFacetJobConfig
          fun $lib => ($defn : IndexBuildM (BuildJob $ty))
      } $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed library facet declaration"

/--
Define a new custom target for the package. Has one form:

```lean
target «target-name» (pkg : Package) : α :=
  /- build function term -/
```

The `pkg` parameter (and its type specifier) is optional.
The term should be of type `IndexBuildM (BuildJob α)`.
-/
scoped macro (name := targetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"target " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$pkg?]? : $ty := $defn $[$wds?]?) =>
    let attr ← withRef kw `(Term.attrInstance| target)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    let pkgName := mkIdentFrom id `_package.name
    let pkg ← expandOptSimpleBinder pkg?
    `(family_def $id : CustomData ($pkgName, $name) := BuildJob $ty
      $[$doc?]? @[$attrs,*] def $id : TargetDecl := {
        pkg := $pkgName
        name := $name
        config := Lake.mkTargetJobConfig
          fun $pkg _ => ($defn : IndexBuildM (BuildJob $ty))
      }  $[$wds?]?)
  | stx => Macro.throwErrorAt stx "ill-formed target declaration"

--------------------------------------------------------------------------------
/-! # External Library Target -/
--------------------------------------------------------------------------------

syntax externLibDeclSpec :=
  ident (ppSpace simpleBinder)? declValSimple

/--
Define a new external library target for the package. Has one form:

```lean
extern_lib «target-name» (pkg : Package) :=
  /- build function term -/
```

The `pkg` parameter (and its type specifier) is optional.
The term should be of type `IndexBuildM (BuildJob FilePath)` and
build the external library's **static** library.
-/
scoped macro (name := externLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"extern_lib " spec:externLibDeclSpec : command => do
  match spec with
  | `(externLibDeclSpec| $id:ident $[$pkg?]? := $defn $[$wds?]?) =>
    let attr ← `(Term.attrInstance| extern_lib)
    let attrs := #[attr] ++ expandAttrs attrs?
    let pkgName := mkIdentFrom id `_package.name
    let targetId := mkIdentFrom id <| id.getId.modifyBase (· ++ `static)
    let name := Name.quoteFrom id id.getId
    `(target $targetId $[$pkg?]? : FilePath := $defn $[$wds?]?
      $[$doc?:docComment]? @[$attrs,*] def $id : ExternLibDecl := {
        pkg := $pkgName
        name := $name
        config := {getJob := ofFamily}
      })
  | stx => Macro.throwErrorAt stx "ill-formed external library declaration"
