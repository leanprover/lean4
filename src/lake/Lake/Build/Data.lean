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

/--
The open type family which maps a module facet's name to its build data
in the Lake build store. For example, the generated C file for `c`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `module_data`).
-/
abbrev ModuleData (facet : Name) := TargetData (`module ++ facet)

instance [h : FamilyOut ModuleData facet α] : FamilyDef TargetData (`module ++ facet) α :=
  ⟨by simp [h.family_key_eq_type]⟩

instance [h : FamilyDef TargetData (`module ++ facet) α] : FamilyDef ModuleData facet α :=
  ⟨h.family_key_eq_type⟩

/--
The open type family which maps a package facet's name to its build data
in the Lake build store. For example, the direct dependencies of the package
for the `deps` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `package_data`).
-/
abbrev PackageData (facet : Name) := TargetData (`package ++ facet)

instance [h : FamilyOut PackageData facet α] : FamilyDef TargetData (`package ++ facet) α :=
  ⟨by simp [h.family_key_eq_type]⟩

instance [h : FamilyDef TargetData (`package ++ facet) α] : FamilyDef PackageData facet α :=
  ⟨h.family_key_eq_type⟩

/-
The open type family which maps a library facet's name to its build data
in the Lake build store. For example, the generated static library for the
 `static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `library_data`).
-/
abbrev LibraryData (facet : Name) := TargetData (`leanLib ++ facet)

instance [h : FamilyOut LibraryData facet α] : FamilyDef TargetData (`leanLib ++ facet) α :=
  ⟨by simp [h.family_key_eq_type]⟩

instance [h : FamilyDef TargetData (`leanLib ++ facet) α] : FamilyDef LibraryData facet α :=
  ⟨h.family_key_eq_type⟩

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
| .facet _ f => TargetData f

instance (priority := low) : FamilyDef BuildData k (BuildData k) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.moduleFacet m f) (ModuleData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.packageFacet p f) (PackageData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.targetFacet p t f) (TargetData f) := ⟨rfl⟩
instance (priority := low) : FamilyDef BuildData (.customTarget p t) (CustomData (p,t)) := ⟨rfl⟩

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

open Parser Command

private def mkFacetDef
  (doc? : Option (TSyntax ``docComment)) (id : Ident) (ty : Term) (kind : Name)
: MacroM Command := do
  let dty := mkCIdentFrom (← getRef) ``TargetData
  let key := Name.quoteFrom id id.getId
  let id := mkIdentFrom id (canonical := true) <| id.getId.modifyBase (kind ++ ·)
  `($[$doc?]? family_def $id : $dty ($(quote kind) ++ $key) := $ty)

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl)
  doc?:optional(docComment) "package_data " id:ident " : " ty:term
: command => mkFacetDef doc? id ty `package

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl)
  doc?:optional(docComment) "module_data " id:ident " : " ty:term
: command => mkFacetDef doc? id ty `module

/-- Macro for declaring new `LibraryData`. -/
scoped macro (name := libraryDataDecl)
  doc?:optional(docComment) "library_data " id:ident " : " ty:term
: command => mkFacetDef doc? id ty `leanLib

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
