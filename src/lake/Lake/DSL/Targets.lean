/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.DSL.DeclUtil
import Lake.Build.Index

/-! # DSL for Targets & Facets
Macros for declaring Lake targets and facets.
-/

namespace Lake.DSL
open Lean Parser Command

syntax buildDeclSig :=
  ident (ppSpace simpleBinder)? Term.typeSpec declValSimple

--------------------------------------------------------------------------------
/-! ## Facet Declarations                                                      -/
--------------------------------------------------------------------------------

abbrev mkModuleFacetDecl
  (α) (facet : Name)
  [FamilyDef ModuleData facet (BuildJob α)]
  (f : Module → FetchM (BuildJob α))
: ModuleFacetDecl := .mk facet <| mkFacetJobConfig fun mod => do
  withRegisterJob (mod.facet facet |>.key.toSimpleString)
    (f mod)

/--
Define a new module facet. Has one form:

```lean
module_facet «facet-name» (mod : Module) : α :=
  /- build term of type `FetchM (BuildJob α)` -/
```

The `mod` parameter (and its type specifier) is optional.
-/
scoped macro (name := moduleFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"module_facet " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$mod?]? : $ty := $defn $[$wds?:whereDecls]?) =>
    let attr ← withRef kw `(Term.attrInstance| module_facet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let facet := Name.quoteFrom id id.getId
    let declId := mkIdentFrom id <| id.getId.modifyBase (.str · "_modFacet")
    let mod ← expandOptSimpleBinder mod?
    `(module_data $id : BuildJob $ty
      $[$doc?:docComment]? @[$attrs,*] abbrev $declId :=
        Lake.DSL.mkModuleFacetDecl $ty $facet (fun $mod => $defn)
      $[$wds?:whereDecls]?)
  | stx => Macro.throwErrorAt stx "ill-formed module facet declaration"

abbrev mkPackageFacetDecl
  (α) (facet : Name)
  [FamilyDef PackageData facet (BuildJob α)]
  (f : Package → FetchM (BuildJob α))
: PackageFacetDecl := .mk facet <| mkFacetJobConfig fun pkg => do
  withRegisterJob (pkg.facet facet |>.key.toSimpleString)
    (f pkg)

/--
Define a new package facet. Has one form:

```lean
package_facet «facet-name» (pkg : Package) : α :=
  /- build term of type `FetchM (BuildJob α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
-/
scoped macro (name := packageFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"package_facet " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$pkg?]? : $ty := $defn $[$wds?:whereDecls]?) =>
    let attr ← withRef kw `(Term.attrInstance| package_facet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let facet := Name.quoteFrom id id.getId
    let declId := mkIdentFrom id <| id.getId.modifyBase (.str · "_pkgFacet")
    let pkg ← expandOptSimpleBinder pkg?
    `(package_data $id : BuildJob $ty
      $[$doc?]? @[$attrs,*] abbrev $declId :=
        Lake.DSL.mkPackageFacetDecl $ty $facet (fun $pkg => $defn)
      $[$wds?:whereDecls]?)
  | stx => Macro.throwErrorAt stx "ill-formed package facet declaration"

abbrev mkLibraryFacetDecl
  (α) (facet : Name)
  [FamilyDef LibraryData facet (BuildJob α)]
  (f : LeanLib → FetchM (BuildJob α))
: LibraryFacetDecl := .mk facet <| mkFacetJobConfig fun lib => do
  withRegisterJob (lib.facet facet |>.key.toSimpleString)
    (f lib)

/--
Define a new library facet. Has one form:

```lean
library_facet «facet-name» (lib : LeanLib) : α :=
  /- build term of type `FetchM (BuildJob α)` -/
```

The `lib` parameter (and its type specifier) is optional.
-/
scoped macro (name := libraryFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"library_facet " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$lib?]? : $ty := $defn $[$wds?:whereDecls]?) =>
    let attr ← withRef kw `(Term.attrInstance| library_facet)
    let attrs := #[attr] ++ expandAttrs attrs?
    let facet := Name.quoteFrom id id.getId
    let declId := mkIdentFrom id <| id.getId.modifyBase (.str · "_libFacet")
    let lib ← expandOptSimpleBinder lib?
    `(library_data $id : BuildJob $ty
      $[$doc?]? @[$attrs,*] abbrev $declId : LibraryFacetDecl :=
        Lake.DSL.mkLibraryFacetDecl $ty $facet (fun $lib => $defn)
      $[$wds?:whereDecls]?)
  | stx => Macro.throwErrorAt stx "ill-formed library facet declaration"

--------------------------------------------------------------------------------
/-! ## Custom Target Declaration                                              -/
--------------------------------------------------------------------------------

abbrev mkTargetDecl
  (α) (pkgName target : Name)
  [FamilyDef CustomData (pkgName, target) (BuildJob α)]
  (f : NPackage pkgName → FetchM (BuildJob α))
: TargetDecl := .mk pkgName target <| mkTargetJobConfig fun pkg => do
  withRegisterJob (pkg.target target |>.key.toSimpleString)
    (f pkg)

/--
Define a new custom target for the package. Has one form:

```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  /- build term of type `FetchM (BuildJob α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.
-/
scoped macro (name := targetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"target " sig:buildDeclSig : command => do
  match sig with
  | `(buildDeclSig| $id:ident $[$pkg?]? : $ty := $defn $[$wds?:whereDecls]?) =>
    let attr ← withRef kw `(Term.attrInstance| target)
    let attrs := #[attr] ++ expandAttrs attrs?
    let name := Name.quoteFrom id id.getId
    let pkgName := mkIdentFrom id `_package.name
    let pkg ← expandOptSimpleBinder pkg?
    `(family_def $id : CustomData ($pkgName, $name) := BuildJob $ty
      $[$doc?]? @[$attrs,*] abbrev $id :=
        Lake.DSL.mkTargetDecl $ty $pkgName $name (fun $pkg => $defn)
      $[$wds?:whereDecls]?)
  | stx => Macro.throwErrorAt stx "ill-formed target declaration"


--------------------------------------------------------------------------------
/-! ## Lean Library & Executable Target Declarations -/
--------------------------------------------------------------------------------

/--
Define a new Lean library target for the package.
Can optionally be provided with a configuration of type `LeanLibConfig`.
Has many forms:

```lean
lean_lib «target-name»
lean_lib «target-name» { /- config opts -/ }
lean_lib «target-name» where /- config opts -/
```
-/
scoped macro (name := leanLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"lean_lib " sig:structDeclSig : command => do
  let attr ← `(Term.attrInstance| lean_lib)
  let ty := mkCIdentFrom (← getRef) ``LeanLibConfig
  let attrs := #[attr] ++ expandAttrs attrs?
  mkConfigDecl none doc? attrs ty sig

@[inherit_doc leanLibDecl] abbrev LeanLibDecl := TSyntax ``leanLibDecl

instance : Coe LeanLibDecl Command where
  coe x := ⟨x.raw⟩

/--
Define a new Lean binary executable target for the package.
Can optionally be provided with a configuration of type `LeanExeConfig`.
Has many forms:

```lean
lean_exe «target-name»
lean_exe «target-name» { /- config opts -/ }
lean_exe «target-name» where /- config opts -/
```
-/
scoped macro (name := leanExeDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"lean_exe " sig:structDeclSig : command => do
  let attr ← `(Term.attrInstance| lean_exe)
  let ty := mkCIdentFrom (← getRef) ``LeanExeConfig
  let attrs := #[attr] ++ expandAttrs attrs?
  mkConfigDecl none doc? attrs ty sig

@[inherit_doc leanExeDecl] abbrev LeanExeDecl := TSyntax ``leanExeDecl

instance : Coe LeanExeDecl Command where
  coe x := ⟨x.raw⟩

--------------------------------------------------------------------------------
/-! ## External Library Target Declaration                                    -/
--------------------------------------------------------------------------------

syntax externLibDeclSpec :=
  ident (ppSpace simpleBinder)? declValSimple

/--
Define a new external library target for the package. Has one form:

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  /- build term of type `FetchM (BuildJob FilePath)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.

The term should build the external library's **static** library.
-/
scoped macro (name := externLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
"extern_lib " spec:externLibDeclSpec : command => do
  match spec with
  | `(externLibDeclSpec| $id:ident $[$pkg?]? := $defn $[$wds?:whereDecls]?) =>
    let attr ← `(Term.attrInstance| extern_lib)
    let attrs := #[attr] ++ expandAttrs attrs?
    let pkgName := mkIdentFrom id `_package.name
    let targetId := mkIdentFrom id <| id.getId.modifyBase (· ++ `static)
    let name := Name.quoteFrom id id.getId
    `(target $targetId $[$pkg?]? : FilePath := $defn $[$wds?:whereDecls]?
      $[$doc?:docComment]? @[$attrs,*] def $id : ExternLibDecl := {
        pkg := $pkgName
        name := $name
        config := {getJob := ofFamily}
      })
  | stx => Macro.throwErrorAt stx "ill-formed external library declaration"
