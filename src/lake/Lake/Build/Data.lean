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
The open type family which maps a (builtin) Lake target's (e.g., `extern_lib`)
facet to its associated build data. For example, an active build target for the
`externLib.static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `target_data`).
-/
opaque TargetData (facet : Name) : Type

/-- The type of the output of the `facet` of objects of `kind`. -/
abbrev FacetData (kind facet : Name) := TargetData (kind ++ facet)

instance [h : FamilyOut (FacetData kind) facet α] : FamilyDef TargetData (kind ++ facet) α :=
  ⟨h.fam_eq⟩

instance [h : FamilyDef TargetData (kind ++ facet) α] : FamilyDef (FacetData kind) facet α :=
  ⟨h.fam_eq⟩

/--
The open type family which maps a module facet's name to its build data
in the Lake build store. For example, the generated C file for `c`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `module_data`).
-/
abbrev ModuleData := FacetData `module

/--
The open type family which maps a package facet's name to its build data
in the Lake build store. For example, the direct dependencies of the package
for the `deps` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `package_data`).
-/
abbrev PackageData := FacetData `package

/--
The open type family which maps a Lean library facet's name to its build data
in the Lake build store. For example, the generated static library for the
`static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `library_data`).
-/
abbrev LibraryData := FacetData `leanLib

@[inherit_doc LibraryData]
abbrev LeanLibData := LibraryData

/--
The type family which maps a Lean executable facet's name to its build data
in the Lake build store. For example, the generated executable for the
`exe` facet.
-/
abbrev LeanExeData := FacetData `leanExe

/--
The type family which maps an external library facet's name to its build data
in the Lake build store. For example, the generated static library for the
`static` facet.
-/
abbrev ExternLibData := FacetData `externLib

/--
The open type family which maps a custom target (package × target name) to
its build data in the Lake build store.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
opaque CustomData (target : Name × Name) : Type

--------------------------------------------------------------------------------
/-! ## Build Data                                                             -/
--------------------------------------------------------------------------------

/--
A mapping between a build key and its associated build data in the store.
It is a simple type function composed of the separate open type families for
modules facets, package facets, Lake target facets, and custom targets.
-/
abbrev BuildData : BuildKey → Type
| .module _ => TargetData `module
| .package _ => TargetData `package
| .packageTarget p t => CustomData (p, t)
| .facet _ k f => FacetData k f

instance (priority := low) : FamilyDef BuildData (.moduleFacet m f) (ModuleData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.packageFacet p f) (PackageData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.facet t k f) (FacetData k f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.customTarget p t) (CustomData (p,t)) := ⟨rfl⟩

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

open Parser Command

/-- Macro for declaring new `FacetData`. -/
scoped macro (name := facetDataDecl)
  doc?:optional(docComment) "facet_data " kind:ident facet:ident " : " ty:term
: command => do
  let dty := mkCIdentFrom (← getRef) ``TargetData
  let kindName := Name.quoteFrom kind kind.getId
  let facetName := Name.quoteFrom facet facet.getId
  let id := mkIdentFrom facet (canonical := true) <|
    facet.getId.modifyBase (kind.getId ++ ·)
  `($[$doc?]? family_def $id : $dty ($kindName ++ $facetName) := $ty)

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl)
  doc?:optional(docComment) "package_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data $(mkIdent `package) $facet : $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl)
  doc?:optional(docComment) "module_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data $(mkIdent `module) $facet : $ty)

/-- Macro for declaring new `LibraryData`. -/
scoped macro (name := libraryDataDecl)
  doc?:optional(docComment) "library_data " facet:ident " : " ty:term
: command => `($[$doc?]? facet_data $(mkIdent `leanLib) $facet : $ty)

/-- Macro for declaring new `TargetData`. -/
scoped macro (name := targetDataDecl)
  doc?:optional(docComment) "target_data " id:ident " : " ty:term
: command => do
  let dty := mkCIdentFrom (← getRef) ``TargetData
  let key := Name.quoteFrom id id.getId
  `($[$doc?]? family_def $id : $dty $key := $ty)

/-- Macro for declaring new `CustomData`. -/
scoped macro (name := customDataDecl)
  doc?:optional(docComment) "custom_data " pkg:ident tgt:ident " : " ty:term
: command => do
  let dty := mkCIdentFrom (← getRef) ``CustomData
  let id := mkIdentFrom tgt (pkg.getId ++ tgt.getId)
  let pkg := Name.quoteFrom pkg pkg.getId
  let tgt := Name.quoteFrom pkg tgt.getId
  `($[$doc?]? family_def $id : $dty ($pkg, $tgt) := $ty)
