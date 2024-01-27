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
  identOrStr (ppSpace simpleBinder)? Term.typeSpec declValSimple

--------------------------------------------------------------------------------
/-! ## Facet Declarations                                                      -/
--------------------------------------------------------------------------------

@[inline]def mkFacetDecl
  (doc? : Option DocComment) (attrs? : Option Attributes)
  (stx : TSyntax ``buildDeclSig) (attr : AttrInstance)
  (fam : Name) (declTy : Name) (suffix : String)
: MacroM Command := do
  match stx with
  | `(buildDeclSig| $nameStx $[$b?]? : $ty := $defn $[$wds?:whereDecls]?) =>
    let name ← expandIdentOrStr nameStx
    let facetId ← expandIdentOrStrAsIdent nameStx
    let declId := mkIdentFrom facetId <| facetId.getId.modifyBase (.str · suffix)
    let b ← expandOptSimpleBinder b?
    let fam := mkIdentFrom (← getRef) fam
    let declTy := mkCIdentFrom (← getRef) declTy
    let attrs := #[attr] ++ expandAttrs attrs?
    `(family_data $facetId : $fam := BuildJob $ty
      $[$doc?:docComment]? @[$attrs,*] abbrev $declId : $declTy := {
        name := $name
        config := Lake.mkFacetJobConfig
          fun $b => ($defn : IndexBuildM (BuildJob $ty))
      } $[$wds?:whereDecls]?)
  | _ => Macro.throwErrorAt stx "ill-formed facet declaration"

/--
Define a new module facet. Has one form:

```lean
module_facet «facet-name» (mod : Module) : α :=
  /- build term of type `IndexBuildM (BuildJob α)` -/
```

The `mod` parameter (and its type specifier) is optional.
-/
scoped macro (name := moduleFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"module_facet " sig:buildDeclSig : command => withRef kw do
  let attr ← `(Term.attrInstance| module_facet)
  mkFacetDecl doc? attrs? sig attr ``ModuleData ``ModuleFacetDecl "_modFacet"

/--
Define a new package facet. Has one form:

```lean
package_facet «facet-name» (pkg : Package) : α :=
  /- build term of type `IndexBuildM (BuildJob α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
-/
scoped macro (name := packageFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"package_facet " sig:buildDeclSig : command => withRef kw do
  let attr ← `(Term.attrInstance| package_facet)
  mkFacetDecl doc? attrs? sig attr ``PackageData ``PackageFacetDecl "_pkgFacet"

/--
Define a new library facet. Has one form:

```lean
library_facet «facet-name» (lib : LeanLib) : α :=
  /- build term of type `IndexBuildM (BuildJob α)` -/
```

The `lib` parameter (and its type specifier) is optional.
-/
scoped macro (name := libraryFacetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"library_facet " sig:buildDeclSig : command => withRef kw do
  let attr ← `(Term.attrInstance| library_facet)
  match sig with
  | `(buildDeclSig| $nameStx $[$b?]? : $ty := $defn $[$wds?:whereDecls]?) =>
    let name ← expandIdentOrStr nameStx
    let facetId ← expandIdentOrStrAsIdent nameStx
    let declid := mkIdentFrom facetId <| facetId.getId.modifyBase (.str · "_libFacet")
    let b ← expandOptSimpleBinder b?
    let attrs := #[attr] ++ expandAttrs attrs?
    `(library_data $facetId : BuildJob $ty
      $[$doc?:docComment]? @[$attrs,*] abbrev $declid : LibraryFacetDecl := {
        name := $name
        config := Lake.mkFacetJobConfig
          fun $b => ($defn : IndexBuildM (BuildJob $ty))
      } $[$wds?:whereDecls]?)
  | _ => Macro.throwErrorAt sig "ill-formed facet declaration"

--------------------------------------------------------------------------------
/-! ## Custom Target Declaration                                              -/
--------------------------------------------------------------------------------

def mkTargetDecl
  (declId : Ident) (name : Term) (ty : Term) (pkg? : Option SimpleBinder) (defn : Term)
  (wds? : Option WhereDecls) (doc? : Option DocComment) (attrs? : Option Attributes)
: MacroM Command := do
  let attr ← `(Term.attrInstance| target)
  let attrs := #[attr] ++ expandAttrs attrs?
  let pkgName := mkIdentFrom name `_package.name
  let pkg ← expandOptSimpleBinder pkg?
  `(family_def $declId : CustomData ($pkgName, $name) := BuildJob $ty
    $[$doc?]? @[$attrs,*] abbrev $declId : TargetDecl := {
      pkg := $pkgName
      name := $name
      config := Lake.mkTargetJobConfig
        fun $pkg => ($defn : IndexBuildM (BuildJob $ty))
    }  $[$wds?:whereDecls]?)

/--
Define a new custom target for the package. Has one form:

```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  /- build term of type `IndexBuildM (BuildJob α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.
-/
scoped macro (name := targetDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"target " sig:buildDeclSig : command => withRef kw do
  match sig with
  | `(buildDeclSig| $nameStx $[$pkg?]? : $ty := $defn $[$wds?:whereDecls]?) =>
    let name ← expandIdentOrStr nameStx
    let declId ← expandIdentOrStrAsIdent nameStx
    mkTargetDecl  declId name ty pkg? defn wds? doc? attrs?
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


--------------------------------------------------------------------------------
/-! ## External Library Target Declaration                                    -/
--------------------------------------------------------------------------------

syntax externLibDeclSpec :=
  identOrStr (ppSpace simpleBinder)? declValSimple

/--
Define a new external library target for the package. Has one form:

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  /- build term of type `IndexBuildM (BuildJob FilePath)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.

The term should build the external library's **static** library.
-/
scoped macro (name := externLibDecl)
doc?:optional(docComment) attrs?:optional(Term.attributes)
kw:"extern_lib " spec:externLibDeclSpec : command => withRef kw do
  match spec with
  | `(externLibDeclSpec| $nameStx $[$pkg?]? := $defn $[$wds?:whereDecls]?) =>
    let attr ← `(Term.attrInstance| extern_lib)
    let attrs := #[attr] ++ expandAttrs attrs?
    let pkgName := mkIdentFrom nameStx `_package.name
    let declId ← expandIdentOrStrAsIdent nameStx
    let targetId := mkIdentFrom declId <| declId.getId.modifyBase (· ++ `static)
    let name ← expandIdentOrStr nameStx
    let tgt ← mkTargetDecl targetId name (mkCIdentFrom kw ``FilePath) pkg? defn wds? none none
    `($tgt $[$doc?:docComment]? @[$attrs,*] def $declId : ExternLibDecl := {
        pkg := $pkgName
        name := $name
        config := {getJob := ofFamily}
      })
  | stx => Macro.throwErrorAt stx "ill-formed external library declaration"
