/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Key
import Lake.Util.Family

open Lean
namespace Lake

--------------------------------------------------------------------------------
/-! ## Build Data Subtypes                                                    -/
--------------------------------------------------------------------------------

/--
The open type family which maps a module facet's name to its build data
in the Lake build store. For example, a transitive × direct import pair
for the `lean.imports` facet or an active build target for `lean.c`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `module_data`).
-/
opaque ModuleData (facet : Name) : Type

/--
The open type family which maps a package facet's name to its build data
in the Lake build store. For example, a transitive dependencies of the package
for the facet `deps`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `package_data`).
-/
opaque PackageData (facet : Name) : Type

/--
The open type family which maps a (builtin) Lake target's (e.g., `extern_lib`)
facet to its associated build data. For example, an active build target for
the `externLib.static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `target_data`).
-/
opaque TargetData (facet : Name) : Type

/-
The open type family which maps a library facet's name to its build data
in the Lake build store. For example, an active build target for the `static`
facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `library_data`).
-/
abbrev LibraryData (facet : Name) := TargetData (`leanLib ++ facet)

instance [h : FamilyOut LibraryData facet α] : FamilyDef TargetData (`leanLib ++ facet) α :=
  ⟨by simp [h.family_key_eq_type]⟩

instance [h : FamilyOut TargetData (`leanLib ++ facet) α] : FamilyDef LibraryData facet α :=
  ⟨h.family_key_eq_type⟩

/--
The open type family which maps a custom target (package × target name) to
its build data in the Lake build store.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
opaque CustomData (target : SimpleName × SimpleName) : Type

--------------------------------------------------------------------------------
/-! ## Build Data                                                             -/
--------------------------------------------------------------------------------

/--
A mapping between a build key and its associated build data in the store.
It is a simple type function composed of the separate open type families for
modules facets, package facets, Lake target facets, and custom targets.
-/
abbrev BuildData : BuildKey → Type
| .moduleFacet _ f => ModuleData f
| .packageFacet _ f => PackageData f
| .targetFacet _ _ f => TargetData f
| .customTarget p t => CustomData (p, t)

instance (priority := low) : FamilyDef BuildData (.moduleFacet m f) (ModuleData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.packageFacet p f) (PackageData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.targetFacet p t f) (TargetData f) := ⟨rfl⟩
instance (priority := low)  : FamilyDef BuildData (.customTarget p t) (CustomData (p,t)) := ⟨rfl⟩

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

open Parser.Command (docComment)

/-- Macro for declaring a new `family_def` whose key is its declaration name. -/
scoped macro (name := familyDataDecl) doc?:optional(docComment)
"family_data " declId:ident " : " fam:ident " := " ty:term : command => do
  let key := Name.quoteFrom declId declId.getId
  `($[$doc?]? family_def $declId : $fam $key := $ty)

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl) doc?:optional(docComment)
"package_data " key:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``PackageData
  `($[$doc?]? family_data $key : $dty := $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl) doc?:optional(docComment)
"module_data " key:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``ModuleData
  `($[$doc?]? family_data $key : $dty := $ty)

/-- Macro for declaring new `TargetData` for libraries. -/
scoped macro (name := libraryDataDecl) doc?:optional(docComment)
"library_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``TargetData
  let key := Name.quoteFrom id id.getId
  let id := mkIdentFrom key <| `leanLib ++ id.getId
  `($[$doc?]? family_def $id : $dty (`leanLib ++ $key) := $ty)

/-- Macro for declaring new `TargetData`. -/
scoped macro (name := targetDataDecl) doc?:optional(docComment)
"target_data " key:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``TargetData
  `($[$doc?]? family_data $key : $dty := $ty)
