/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.DSL.DeclUtil
import Lake.Build.Index

/-! # DSL for Targets & Facets
Macros for declaring Lake targets and facets.
-/

open System (FilePath)
open Lean Parser Elab Command

namespace Lake.DSL

syntax buildDeclSig :=
  identOrStr (ppSpace simpleBinder)? Term.typeSpec declValSimple

--------------------------------------------------------------------------------
/-! ## Facet Declarations                                                      -/
--------------------------------------------------------------------------------

abbrev mkModuleFacetDecl
  (α) (facet : Name)
  [FormatQuery α] [FamilyDef ModuleData facet α]
  (f : Module → FetchM (Job α))
: ModuleFacetDecl := .mk facet <| mkFacetJobConfig fun mod => do
  withRegisterJob (mod.facet facet |>.key.toSimpleString)
    (f mod)

/--
Define a new module facet. Has one form:

```lean
module_facet «facet-name» (mod : Module) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `mod` parameter (and its type specifier) is optional.
-/
scoped syntax (name := moduleFacetDecl)
(docComment)? (Term.attributes)? "module_facet " buildDeclSig : command

@[builtin_macro moduleFacetDecl]
def expandModuleFacetDecl : Macro := fun stx => do
  let `(moduleFacetDecl|$(doc?)? $(attrs?)? module_facet%$kw $sig) := stx
    | Macro.throwErrorAt stx "ill-formed module facet declaration"
  let `(buildDeclSig| $nameStx $[$mod?]? : $ty := $defn $[$wds?:whereDecls]?) := sig
    | Macro.throwErrorAt sig "ill-formed module facet declaration"
  withRef kw do
  let attr ← `(Term.attrInstance| «module_facet»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let id := expandIdentOrStrAsIdent nameStx
  let facet := Name.quoteFrom id id.getId
  let declId := mkIdentFrom id <| id.getId.modifyBase (.str · "_modFacet")
  let mod ← expandOptSimpleBinder mod?
  `(module_data $id : $ty
    $[$doc?:docComment]? @[$attrs,*] abbrev $declId :=
      Lake.DSL.mkModuleFacetDecl $ty $facet (fun $mod => $defn)
    $[$wds?:whereDecls]?)

abbrev mkPackageFacetDecl
  (α) (facet : Name)
  [FormatQuery α] [FamilyDef PackageData facet α]
  (f : Package → FetchM (Job α))
: PackageFacetDecl := .mk facet <| mkFacetJobConfig fun pkg => do
  withRegisterJob (pkg.facet facet |>.key.toSimpleString)
    (f pkg)

/--
Define a new package facet. Has one form:

```lean
package_facet «facet-name» (pkg : Package) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
-/
scoped syntax (name := packageFacetDecl)
(docComment)? (Term.attributes)? "package_facet " buildDeclSig : command

@[builtin_macro packageFacetDecl]
def expandPackageFacetDecl : Macro := fun stx => do
  let `(packageFacetDecl|$(doc?)? $(attrs?)? package_facet%$kw $sig) := stx
    | Macro.throwErrorAt stx "ill-formed package facet declaration"
  let `(buildDeclSig| $nameStx $[$pkg?]? : $ty := $defn $[$wds?:whereDecls]?) := sig
    | Macro.throwErrorAt sig "ill-formed package facet signature"
  withRef kw do
  let attr ← `(Term.attrInstance| «package_facet»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let id := expandIdentOrStrAsIdent nameStx
  let facet := Name.quoteFrom id id.getId
  let declId := mkIdentFrom id <| id.getId.modifyBase (.str · "_pkgFacet")
  let pkg ← expandOptSimpleBinder pkg?
  `(package_data $id : $ty
    $[$doc?]? @[$attrs,*] abbrev $declId :=
      Lake.DSL.mkPackageFacetDecl $ty $facet (fun $pkg => $defn)
    $[$wds?:whereDecls]?)

abbrev mkLibraryFacetDecl
  (α) (facet : Name)
  [FormatQuery α] [FamilyDef LibraryData facet α]
  (f : LeanLib → FetchM (Job α))
: LibraryFacetDecl := .mk facet <| mkFacetJobConfig fun lib => do
  withRegisterJob (lib.facet facet |>.key.toSimpleString)
    (f lib)

/--
Define a new library facet. Has one form:

```lean
library_facet «facet-name» (lib : LeanLib) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `lib` parameter (and its type specifier) is optional.
-/
scoped syntax (name := libraryFacetDecl)
(docComment)? (Term.attributes)? "library_facet " buildDeclSig : command

@[builtin_macro libraryFacetDecl]
def expandLibraryFacetDecl : Macro := fun stx => do
  let `(libraryFacetDecl|$(doc?)? $(attrs?)? library_facet%$kw $sig) := stx
    | Macro.throwErrorAt stx "ill-formed library facet declaration"
  let `(buildDeclSig| $nameStx  $[$lib?]? : $ty := $defn $[$wds?:whereDecls]?) := sig
    | Macro.throwErrorAt sig "ill-formed library facet signature"
  withRef kw do
  let attr ← `(Term.attrInstance| «library_facet»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let id := expandIdentOrStrAsIdent nameStx
  let facet := Name.quoteFrom id id.getId
  let declId := mkIdentFrom id <| id.getId.modifyBase (.str · "_libFacet")
  let lib ← expandOptSimpleBinder lib?
  `(library_data $id : $ty
    $[$doc?]? @[$attrs,*] abbrev $declId : LibraryFacetDecl :=
      Lake.DSL.mkLibraryFacetDecl $ty $facet (fun $lib => $defn)
    $[$wds?:whereDecls]?)


--------------------------------------------------------------------------------
/-! ## Custom Target Declaration                                              -/
--------------------------------------------------------------------------------

abbrev mkTargetDecl
  (α) (pkgName target : Name)
  [FormatQuery α] [FamilyDef CustomData (pkgName, target) α]
  (f : NPackage pkgName → FetchM (Job α))
: TargetDecl := .mk pkgName target <| mkTargetJobConfig fun pkg => do
  withRegisterJob (pkg.target target |>.key.toSimpleString)
    (f pkg)

/--
Define a new custom target for the package. Has one form:

```lean
target «target-name» (pkg : NPackage _package.name) : α :=
  /- build term of type `FetchM (Job α)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.
-/
scoped syntax (name := targetDecl)
(docComment)? (Term.attributes)? "target " buildDeclSig : command

@[builtin_macro targetDecl]
def expandTargetDecl : Macro := fun stx => do
  let `(targetDecl|$(doc?)? $(attrs?)? target%$kw $sig) := stx
    | Macro.throwErrorAt stx "ill-formed target declaration"
  let `(buildDeclSig|$id:ident $[$pkg?]? : $ty := $defn $[$wds?:whereDecls]?) := sig
    | Macro.throwErrorAt sig "ill-formed target signature"
  withRef kw do
  let attr ← `(Term.attrInstance| «target»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let name := Name.quoteFrom id id.getId
  let pkgName := mkIdentFrom id `_package.name
  let pkg ← expandOptSimpleBinder pkg?
  `(family_def $id : CustomData ($pkgName, $name) := $ty
    $[$doc?]? @[$attrs,*] abbrev $id :=
      Lake.DSL.mkTargetDecl $ty $pkgName $name (fun $pkg => $defn)
    $[$wds?:whereDecls]?)

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
scoped syntax (name := leanLibDecl)
(docComment)? (Term.attributes)? "lean_lib " structDeclSig : command

@[builtin_command_elab leanLibDecl]
def elabLeanLibDecl : CommandElab := fun stx => do
  let `(leanLibDecl|$(doc?)? $(attrs?)? lean_lib%$kw $sig) := stx
    | throwErrorAt stx "ill-formed lean_lib declaration"
  withRef kw do
  let attr ← `(Term.attrInstance| «lean_lib»)
  let attrs := #[attr] ++ expandAttrs attrs?
  elabConfigDecl ``LeanLibConfig sig doc? attrs

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
scoped syntax (name := leanExeDecl)
(docComment)? (Term.attributes)? "lean_exe " structDeclSig : command

@[builtin_command_elab leanExeDecl]
def elabLeanExeDecl : CommandElab := fun stx => do
  let `(leanExeDecl|$(doc?)? $(attrs?)? lean_exe%$kw $sig) := stx
    | throwErrorAt stx "ill-formed lean_exe declaration"
  withRef kw do
  let attr ← `(Term.attrInstance| «lean_exe»)
  let attrs := #[attr] ++ expandAttrs attrs?
  elabConfigDecl ``LeanExeConfig sig doc? attrs

@[inherit_doc leanExeDecl] abbrev LeanExeDecl := TSyntax ``leanExeDecl

instance : Coe LeanExeDecl Command where
  coe x := ⟨x.raw⟩

--------------------------------------------------------------------------------
/-! ## External Library Target Declaration                                    -/
--------------------------------------------------------------------------------

abbrev mkExternLibDecl
  (pkgName name : Name)
  [FamilyDef CustomData (pkgName, .str name "static")  FilePath]
: ExternLibDecl := .mk pkgName name {getPath := cast (by simp)}

syntax externLibDeclSpec :=
  identOrStr (ppSpace simpleBinder)? declValSimple

/--
Define a new external library target for the package. Has one form:

```lean
extern_lib «target-name» (pkg : NPackage _package.name) :=
  /- build term of type `FetchM (Job FilePath)` -/
```

The `pkg` parameter (and its type specifier) is optional.
It is of type `NPackage _package.name` to provably demonstrate the package
provided is the package in which the target is defined.

The term should build the external library's **static** library.
-/
scoped syntax (name := externLibDecl)
(docComment)? (Term.attributes)? "extern_lib " externLibDeclSpec : command

@[builtin_macro externLibDecl]
def expandExternLibDecl : Macro := fun stx => do
  let `(externLibDecl|$(doc?)? $(attrs?)? extern_lib%$kw $spec) := stx
    | Macro.throwErrorAt stx "ill-formed external library declaration"
  let `(externLibDeclSpec| $nameStx $[$pkg?]? := $defn $[$wds?:whereDecls]?) := spec
    | Macro.throwErrorAt spec "ill-formed external library signature"
  withRef kw do
  let attr ← `(Term.attrInstance| «extern_lib»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let id := expandIdentOrStrAsIdent nameStx
  let pkgName := mkIdentFrom id `_package.name
  let targetId := mkIdentFrom id <| id.getId.modifyBase (· ++ `static)
  let name := Name.quoteFrom id id.getId
  `(target $targetId:ident $[$pkg?]? : FilePath := $defn $[$wds?:whereDecls]?
    $[$doc?:docComment]? @[$attrs,*] def $id : ExternLibDecl :=
      Lake.DSL.mkExternLibDecl $pkgName $name)
