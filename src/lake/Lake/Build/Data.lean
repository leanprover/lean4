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
The open type family which maps a facet to its build data in
the Lake build store. For example, the imports of a module.

It is an open type, meaning additional mappings can be add lazily
as needed (via `facet_data`).
-/
abbrev FacetData (kind facet : Name) := TargetData (kind ++ facet)

instance [h : FamilyDef TargetData (kind ++ facet) α] : FamilyDef (FacetData kind) facet α :=
  ⟨h.fam_eq⟩

/--
The open type family which maps a module facet's name to its build data
in the Lake build store. For example, the generated C file for `c`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `module_data`).
-/
abbrev ModuleData := FacetData Module.facetKind

/--
The open type family which maps a package facet's name to its build data
in the Lake build store. For example, the direct dependencies of the package
for the `deps` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `package_data`).
-/
abbrev PackageData := FacetData Package.facetKind

/-- The kind identifier for facets of a Lean library. -/
abbrev LeanLib.facetKind : Name := `leanLib

/--
The open type family which maps a Lean library facet's name to its build data
in the Lake build store. For example, the generated static library for the
`static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `library_data`).
-/
abbrev LibraryData := FacetData LeanLib.facetKind

@[inherit_doc LibraryData]
abbrev LeanLibData := LibraryData

/-- The kind identifier for facets of a Lean executable. -/
abbrev LeanExe.facetKind : Name := `leanExe

/--
The type family which maps a Lean executable facet's name to its build data
in the Lake build store. For example, the generated executable for the
`exe` facet.
-/
abbrev LeanExeData := FacetData LeanExe.facetKind

/-- The kind identifier for facets of an external library. -/
abbrev ExternLib.facetKind : Name := `externLib

/--
The type family which maps an external library facet's name to its build data
in the Lake build store. For example, the generated static library for the
`static` facet.
-/
abbrev ExternLibData := FacetData ExternLib.facetKind

/--
The open type family which maps a custom package target
(package × target name) to its build data in the Lake build store.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
opaque CustomDataFam (target : Name × Name) : Type

/--
The open type family which maps a custom package target
to its build data in the Lake build store.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
abbrev CustomData (package target : Name) := CustomDataFam (package, target)

instance [h : FamilyDef CustomDataFam (p, t) α] : FamilyDef (CustomData p) t α :=
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
| .module _ => TargetData Module.facetKind
| .package _ => TargetData Package.facetKind
| .packageTarget p t .anonymous => CustomData p t
| .packageTarget _ _ k => TargetData k
| .facet t f => FacetData t.kind f

instance (priority := low) : FamilyDef BuildData (.moduleFacet m f) (ModuleData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.packageFacet p f) (PackageData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.customTarget p t) (CustomData p t) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.facet t f) (FacetData t.kind f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.targetFacet p t LeanLib.facetKind f) (LeanLibData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.targetFacet p t LeanExe.facetKind f) (LeanExeData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.targetFacet p t ExternLib.facetKind f) (ExternLibData f) := ⟨rfl⟩

instance [FamilyOut TargetData Module.facetKind α]
: FamilyDef BuildData (.module k) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData Package.facetKind α]
: FamilyDef BuildData (.package k) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData LeanLib.facetKind α]
: FamilyDef BuildData (.packageTarget p t LeanLib.facetKind) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData LeanExe.facetKind α]
: FamilyDef BuildData (.packageTarget p t LeanExe.facetKind) α where
  fam_eq := by unfold BuildData; simp

instance [FamilyOut TargetData ExternLib.facetKind α]
: FamilyDef BuildData (.packageTarget p t ExternLib.facetKind) α where
  fam_eq := by unfold BuildData; simp

theorem BuildKey.data_eq_of_kind {k : BuildKey} :
  ¬ k.kind.isAnonymous → (BuildData k) = TargetData k.kind
:= by unfold BuildData; split <;> simp [BuildKey.kind, Lean.Name.isAnonymous]

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

open Parser Command

/-- Macro for declaring new `FacetData`. -/
scoped macro (name := facetDataDecl)
  doc?:optional(docComment) "facet_data " kind:ident facet:ident " : " ty:term
: command => do
  let fam := mkCIdentFrom (← getRef) ``TargetData
  let kindName := Name.quoteFrom kind kind.getId
  let facetName := Name.quoteFrom facet facet.getId
  let id := mkIdentFrom facet (canonical := true) <|
    facet.getId.modifyBase (kind.getId ++ ·)
  `($[$doc?]? family_def $id : $fam ($kindName ++ $facetName) := $ty)

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl)
  doc?:optional(docComment) "package_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data $(mkIdent Package.facetKind) $facet : $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl)
  doc?:optional(docComment) "module_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data $(mkIdent Module.facetKind) $facet : $ty)

/-- Macro for declaring new `LibraryData`. -/
scoped macro (name := libraryDataDecl)
  doc?:optional(docComment) "library_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data $(mkIdent LeanLib.facetKind) $facet : $ty)

/-- Macro for declaring new `TargetData`. -/
scoped macro (name := targetDataDecl)
  doc?:optional(docComment) "target_data " id:ident " : " ty:term
: command => do
  let fam := mkCIdentFrom (← getRef) ``TargetData
  let idx := Name.quoteFrom id id.getId
  `($[$doc?]? family_def $id : $fam $idx := $ty)

/-- Macro for declaring new `CustomData`. -/
scoped macro (name := customDataDecl)
  doc?:optional(docComment) "custom_data " pkg:ident tgt:ident " : " ty:term
: command => do
  let fam := mkCIdentFrom (← getRef) ``CustomDataFam
  let id := mkIdentFrom tgt (pkg.getId ++ tgt.getId)
  let pkg := Name.quoteFrom pkg pkg.getId
  let tgt := Name.quoteFrom pkg tgt.getId
  `($[$doc?]? family_def $id : $fam ($pkg, $tgt) := $ty)
