/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Key
import Lake.Util.Family

open Lean
namespace Lake

--------------------------------------------------------------------------------
/-! ## Build Data Subtypes                                                    -/
--------------------------------------------------------------------------------

/--
The open type family which maps a Lake target to its associated build data.
For example, the generated static library for the `externLib.static` facet of
an external library.

It is an open type, meaning additional mappings can be add lazily
as needed (via `target_data`).
-/
opaque TargetData (name : Name) : Type

/--
The open type family which maps a Lake facet to its output type.
For example, a `FilePath` for the `module.olean` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `facet_data`).
-/
opaque FacetOut (facet : Name) : Type

/--
The open type family which maps a Lake facet kind and name to its output type.
For example, a `FilePath` for the `module` `olean` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `facet_data`).
-/
abbrev FacetData (kind facet : Name) := FacetOut (kind ++ facet)

instance [h : FamilyDef FacetOut (kind ++ facet) α] : FamilyDef (FacetData kind) facet α :=
  ⟨h.fam_eq⟩

instance [h :  FamilyDef (FacetData kind) facet α] : FamilyDef FacetOut (kind ++ facet) α :=
  ⟨h.fam_eq⟩

/--
The open type family which maps a module facet's name to its output type.
For example, a `FilePath` for the module `olean` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `module_data`).
-/
abbrev ModuleData := FacetData Module.KIND

/--
The open type family which maps a package facet's name to output type.
For example, an `Arrry Package` of direct dependencies for the `deps` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `package_data`).
-/
abbrev PackageData := FacetData Package.KIND

/-- The kind identifier for facets and configurations of a Lean library. -/
abbrev LeanLib.KIND : Name := `leanLib

/--
The open type family which maps a Lean library facet's name to its output type.
For example, the `FilePath` pf the generated static library for the `static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `library_data`).
-/
abbrev LibraryData := FacetData LeanLib.KIND

@[inherit_doc LibraryData]
abbrev LeanLibData := LibraryData

/-- The kind identifier for facets and configurations of a Lean executable. -/
abbrev LeanExe.KIND : Name := `leanExe

/--
The type family which maps a Lean executable facet's name to its output type.
For example, the `FilePath` of the executable for the `exe` facet.
-/
abbrev LeanExeData := FacetData LeanExe.KIND

/-- The kind identifier for facets and configurations of an external library. -/
abbrev ExternLib.KIND : Name := `externLib

/--
The type family which maps an external library facet's name to its output type.
For example, the `FilePath` of the generated static library for the `static` facet.
-/
abbrev ExternLibData := FacetData ExternLib.KIND

/--
The open type family which maps a custom package target
(package × target name) to its output type.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
opaque CustomOut (target : Name × Name) : Type

/--
The open type family which maps a custom package targetto its output type.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
abbrev CustomData (package target : Name) := CustomOut (package, target)

instance [h : FamilyDef CustomOut (p, t) α] : FamilyDef (CustomData p) t α :=
  ⟨h.fam_eq⟩

--------------------------------------------------------------------------------
/-! ## Build Data                                                             -/
--------------------------------------------------------------------------------

/--
A mapping between a build key and its associated build data in the store.
It is a simple type function composed of the separate open type families for
modules facets, package facets, Lake target facets, and custom targets.
-/
abbrev BuildData : BuildKey → Type
| .module _ => TargetData Module.KIND
| .package _ => TargetData Package.KIND
| .packageTarget p t .anonymous => CustomData p t
| .packageTarget _ _ k => TargetData k
| .facet _ f => FacetOut f

instance (priority := low) : FamilyDef BuildData (.customTarget p t) (CustomData p t) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.facet t f) (FacetOut f) := ⟨rfl⟩

instance [FamilyOut TargetData Module.KIND α]
: FamilyDef BuildData (.module k) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData Package.KIND α]
: FamilyDef BuildData (.package k) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData LeanLib.KIND α]
: FamilyDef BuildData (.packageTarget p t LeanLib.KIND) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData LeanExe.KIND α]
: FamilyDef BuildData (.packageTarget p t LeanExe.KIND) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData ExternLib.KIND α]
: FamilyDef BuildData (.packageTarget p t ExternLib.KIND) α where
  fam_eq := by unfold BuildData; simp

theorem BuildKey.data_eq_of_kind {k : BuildKey} :
  ¬ k.kind.isAnonymous → (BuildData k) = TargetData k.kind
:= by unfold BuildData; split <;> simp [BuildKey.kind, Lean.Name.isAnonymous]

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

open Parser Command

/-- Internal macro for declaring new facet within Lake. -/
scoped macro (name := builtinFacetCommand)
  doc?:optional(docComment) tk:"builtin_facet " id:ident kind:ident name:ident " : " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom tk ``FacetOut
  let nameLit := Name.quoteFrom name name.getId
  let kindLit := Name.quoteFrom kind kind.getId
  let facet := kind.getId ++ name.getId
  let facetId := mkIdentFrom tk facet (canonical := true)
  let facetLit := Name.quoteFrom tk facet
  `(
    $[$doc?]? abbrev $id := $facetLit
    family_def $facetId : $fam $facetLit := $ty
    instance : FamilyDef FacetOut ($kindLit ++ $nameLit) $ty :=
      inferInstanceAs (FamilyDef FacetOut $facetLit $ty)
  )

/-- Macro for declaring new `FacetData`. -/
scoped macro (name := facetDataDecl)
  doc?:optional(docComment) tk:"facet_data " kind:ident name:ident " : " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom tk ``FacetOut
  let kindLit := Name.quoteFrom kind kind.getId
  let nameLit := Name.quoteFrom name name.getId
  let facet := kind.getId ++ name.getId
  let facetLit := Name.quoteFrom tk facet
  let id := mkIdentFrom tk facet (canonical := true)
  `($[$doc?]? family_def $id : $fam $facetLit := $ty
    instance : FamilyDef FacetOut ($kindLit ++ $nameLit) $ty :=
      inferInstanceAs (FamilyDef FacetOut $facetLit $ty))

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl)
  doc?:optional(docComment) tk:"package_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data%$tk $(mkIdentFrom tk Package.KIND) $facet : $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl)
  doc?:optional(docComment) tk:"module_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data%$tk $(mkIdentFrom tk Module.KIND) $facet : $ty)

/-- Macro for declaring new `LibraryData`. -/
scoped macro (name := libraryDataDecl)
  doc?:optional(docComment) tk:"library_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data%$tk $(mkIdentFrom tk LeanLib.KIND) $facet : $ty)

/-- Macro for declaring new `TargetData`. -/
scoped macro (name := targetDataDecl)
  doc?:optional(docComment) tk:"target_data " id:ident " : " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom (← getRef) ``TargetData
  let idx := Name.quoteFrom id id.getId
  `($[$doc?]? family_def $id : $fam $idx := $ty)

/-- Macro for declaring new `CustomData`. -/
scoped macro (name := customDataDecl)
  doc?:optional(docComment) tk:"custom_data " pkg:ident tgt:ident " : " ty:term
: command => withRef tk do
  let fam := mkCIdentFrom (← getRef) ``CustomOut
  let id := mkIdentFrom tgt (pkg.getId ++ tgt.getId)
  let pkg := Name.quoteFrom pkg pkg.getId
  let tgt := Name.quoteFrom pkg tgt.getId
  `($[$doc?]? family_def $id : $fam ($pkg, $tgt) := $ty)
