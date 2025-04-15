/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.DSL.DeclUtil
import Lake.Config.FacetConfig
import Lake.Config.TargetConfig
import Lake.Build.Job

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
  [OptDataKind α] [FormatQuery α] [FamilyDef ModuleData facet α]
  (f : Module → FetchM (Job α))
: ModuleFacetDecl := .mk (Module.facetKind ++ facet) <| mkFacetJobConfig fun mod => do
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
  [OptDataKind α] [FormatQuery α] [FamilyDef PackageData facet α]
  (f : Package → FetchM (Job α))
: PackageFacetDecl := .mk (Package.facetKind ++ facet) <| mkFacetJobConfig fun pkg => do
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
  [OptDataKind α] [FormatQuery α] [FamilyDef LibraryData facet α]
  (f : LeanLib → FetchM (Job α))
: LibraryFacetDecl := .mk (LeanLib.facetKind ++ facet) <| mkFacetJobConfig fun lib => do
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
  [OptDataKind α] [FormatQuery α] [FamilyDef (CustomData pkgName) target α]
  (f : NPackage pkgName → FetchM (Job α))
: TargetDecl :=
  let cfg := mkTargetJobConfig fun pkg => do
    withRegisterJob (pkg.target target |>.key.toSimpleString) do
      f pkg
  .mk (.mk pkgName target .anonymous (.mk cfg) (by simp [Name.isAnonymous])) rfl

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
scoped syntax (name := targetCommand)
(docComment)? (Term.attributes)? "target " buildDeclSig : command

@[builtin_macro targetCommand]
def expandTargetCommand : Macro := fun stx => do
  let `(targetCommand|$(doc?)? $(attrs?)? target%$kw $sig) := stx
    | Macro.throwErrorAt stx "ill-formed target declaration"
  let `(buildDeclSig|$id:ident $[$pkg?]? : $ty := $defn $[$wds?:whereDecls]?) := sig
    | Macro.throwErrorAt sig "ill-formed target signature"
  withRef kw do
  let attr ← `(Term.attrInstance| «target»)
  let attrs := #[attr] ++ expandAttrs attrs?
  let name := Name.quoteFrom id id.getId
  let pkgName := mkIdentFrom id (packageDeclName.str "name")
  let pkg ← expandOptSimpleBinder pkg?
  `(family_def $id : CustomOut ($pkgName, $name) := $ty
    $[$doc?]? abbrev $id :=
      Lake.DSL.mkTargetDecl $ty $pkgName $name (fun $pkg => $defn)
    $[$wds?:whereDecls]?
    @[$attrs,*] def configDecl : ConfigDecl := $(id).toConfigDecl)

--------------------------------------------------------------------------------
/-! ## Lean Library & Executable Target Declarations -/
--------------------------------------------------------------------------------

abbrev mkConfigDecl
  (pkg name kind : Name)
  (config : ConfigType kind pkg name)
  [FamilyDef (CustomData pkg) name (ConfigTarget kind)]
  [FamilyDef DataType kind (ConfigTarget kind)]
: KConfigDecl kind :=
  {pkg, name, kind, config, wf_data := fun _ => by simp, kind_eq := rfl}

def mkConfigDeclDef
  (tyName attr kind : Name)
  [ConfigInfo tyName] [delTyName : TypeName (KConfigDecl kind)]
  (doc? : Option DocComment) (attrs? : Option Attributes)
  (nameStx? : Option IdentOrStr) (cfg : OptConfig)
: CommandElabM Command := do
  let configId : Ident ← `(config)
  let id ← mkConfigDeclIdent nameStx?
  let name := Name.quoteFrom id id.getId
  let ty := Syntax.mkCApp tyName #[name]
  elabConfig tyName configId ty cfg
  let attrId ← mkIdentFromRef attr
  let targetAttr ← `(Term.attrInstance| «target»)
  let kindAttr ← `(Term.attrInstance| $attrId:ident)
  let attrs := #[targetAttr, kindAttr] ++ expandAttrs attrs?
  let pkg ← mkIdentFromRef (packageDeclName.str "name")
  let declTy ← mkIdentFromRef delTyName.typeName
  let kind := Name.quoteFrom (← getRef) kind
  `(family_def $id : CustomOut ($pkg, $name) := ConfigTarget $kind
    $[$doc?]? abbrev $id : $declTy :=
      Lake.DSL.mkConfigDecl $pkg $name $kind $configId
    @[$attrs,*] def configDecl : ConfigDecl := $(id).toConfigDecl
  )

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
scoped syntax (name := leanLibCommand)
(docComment)? (Term.attributes)? "lean_lib " (identOrStr)? optConfig : command

@[builtin_command_elab leanLibCommand]
def elabLeanLibCommand : CommandElab := fun stx => do
  let `(leanLibCommand|$(doc?)? $(attrs?)? lean_lib%$kw $(nameStx?)? $cfg) := stx
    | throwErrorAt stx "ill-formed lean_lib declaration"
  withRef kw do
  let cmd ← mkConfigDeclDef ``LeanLibConfig LeanLib.keyword LeanLib.configKind doc? attrs? nameStx? cfg
  withMacroExpansion stx cmd <| elabCommand cmd

@[inherit_doc leanLibCommand] abbrev LeanLibCommand := TSyntax ``leanLibCommand

instance : Coe LeanLibCommand Command where
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
scoped syntax (name := leanExeCommand)
(docComment)? (Term.attributes)? "lean_exe " (identOrStr)? optConfig : command

@[builtin_command_elab leanExeCommand]
def elabLeanExeCommand : CommandElab := fun stx => do
  let `(leanExeCommand|$(doc?)? $(attrs?)? lean_exe%$kw $(nameStx?)? $cfg) := stx
    | throwErrorAt stx "ill-formed lean_exe declaration"
  withRef kw do
  let cmd ← mkConfigDeclDef ``LeanExeConfig LeanExe.keyword LeanExe.configKind doc? attrs? nameStx? cfg
  withMacroExpansion stx cmd <| elabCommand cmd

@[inherit_doc leanExeCommand] abbrev LeanExeCommand := TSyntax ``leanExeCommand

instance : Coe LeanExeCommand Command where
  coe x := ⟨x.raw⟩

/--
Define a new input file target for the package.
Can optionally be provided with a configuration of type `InputFileConfig`.
-/
scoped syntax (name := inputFileCommand)
(docComment)? (Term.attributes)? "input_file " (identOrStr)? optConfig : command

@[builtin_command_elab inputFileCommand]
def elabInputfileCommand : CommandElab := fun stx => do
  let `(inputFileCommand|$(doc?)? $(attrs?)? input_file%$kw $(nameStx?)? $cfg) := stx
    | throwErrorAt stx "ill-formed input_file declaration"
  withRef kw do
  let cmd ← mkConfigDeclDef ``InputFileConfig InputFile.keyword InputFile.configKind doc? attrs? nameStx? cfg
  withMacroExpansion stx cmd <| elabCommand cmd

@[inherit_doc inputFileCommand] abbrev InputFileCommand := TSyntax ``inputFileCommand

instance : Coe InputFileCommand Command where
  coe x := ⟨x.raw⟩

/--
Define a new input directory target for the package.
Can optionally be provided with a configuration of type `InputDirConfig`.
-/
scoped syntax (name := inputDirCommand)
(docComment)? (Term.attributes)? "input_dir " (identOrStr)? optConfig : command

@[builtin_command_elab inputDirCommand]
def elabInputDirCommand : CommandElab := fun stx => do
  let `(inputDirCommand|$(doc?)? $(attrs?)? input_dir%$kw $(nameStx?)? $cfg) := stx
    | throwErrorAt stx "ill-formed input_dir declaration"
  withRef kw do
  let cmd ← mkConfigDeclDef ``InputDirConfig InputDir.keyword InputDir.configKind doc? attrs? nameStx? cfg
  withMacroExpansion stx cmd <| elabCommand cmd

@[inherit_doc inputDirCommand] abbrev InputDirCommand := TSyntax ``inputDirCommand

instance : Coe InputDirCommand Command where
  coe x := ⟨x.raw⟩

--------------------------------------------------------------------------------
/-! ## External Library Target Declaration                                    -/
--------------------------------------------------------------------------------

abbrev mkExternLibDecl
  (pkgName name : Name)
  [FamilyDef (CustomData pkgName) (.str name "static") FilePath]
  [FamilyDef (CustomData pkgName) name (ConfigTarget ExternLib.configKind)]
: ExternLibDecl :=
  mkConfigDecl pkgName name ExternLib.configKind {getPath := cast (by simp)}

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
scoped syntax (name := externLibCommand)
(docComment)? (Term.attributes)? "extern_lib " externLibDeclSpec : command

@[builtin_macro externLibCommand]
def expandExternLibCommand : Macro := fun stx => do
  let `(externLibCommand|$(doc?)? $(attrs?)? extern_lib%$kw $spec) := stx
    | Macro.throwErrorAt stx "ill-formed external library declaration"
  let `(externLibDeclSpec| $nameStx $[$pkg?]? := $defn $[$wds?:whereDecls]?) := spec
    | Macro.throwErrorAt spec "ill-formed external library signature"
  withRef kw do
  let attr1 ← `(Term.attrInstance| «target»)
  let attr2 ← `(Term.attrInstance| «extern_lib»)
  let attrs := #[attr1, attr2] ++ expandAttrs attrs?
  let id := expandIdentOrStrAsIdent nameStx
  let pkgName := mkIdentFrom kw (packageDeclName.str "name")
  let targetId := mkIdentFrom id <| id.getId.modifyBase (· ++ `static)
  let name := Name.quoteFrom id id.getId
  let kind := Name.quoteFrom kw ExternLib.configKind
  `(target $targetId:ident $[$pkg?]? : FilePath := $defn $[$wds?:whereDecls]?
    family_def $id : CustomOut ($pkgName, $name) := ConfigTarget $kind
    $[$doc?:docComment]? def $id : ExternLibDecl :=
      Lake.DSL.mkExternLibDecl $pkgName $name
    @[$attrs,*] def configDecl : ConfigDecl := $(id).toConfigDecl)
