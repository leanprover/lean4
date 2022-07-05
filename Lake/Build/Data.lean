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
The open type family which maps a module facet's name to it build data
in the Lake build store. For example, a transitive × direct import pair
for the `lean.imports` facet or an active build target for `lean.c`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `module_data`).
-/
opaque ModuleData (facet : WfName) : Type

/--
The open type family which maps a package facet's name to it build data
in the Lake build store. For example, a transitive dependencies of the package
for the facet `deps`.

It is an open type, meaning additional mappings can be add lazily
as needed (via `package_data`).
-/
opaque PackageData (facet : WfName) : Type

/--
The open type family which maps a (builtin) Lake target's (e.g., `extern_lib`)
facet to its associated build data. For example, an active build target for
the `externLib.static` facet.

It is an open type, meaning additional mappings can be add lazily
as needed (via `target_data`).
-/
opaque TargetData (facet : WfName) : Type

/--
The open type family which maps a custom target (package × target name) to
its build data in the Lake build store.

It is an open type, meaning additional mappings can be add lazily
as needed (via `custom_data`).
-/
opaque CustomData (target : WfName × WfName) : Type

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

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl) doc?:optional(Parser.Command.docComment)
"package_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``PackageData
  let key := WfName.quoteNameFrom id id.getId
  `($[$doc?]? family_def $id : $dty $key := $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl) doc?:optional(Parser.Command.docComment)
"module_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``ModuleData
  let key := WfName.quoteNameFrom id id.getId
  `($[$doc?]? family_def $id : $dty $key := $ty)

/-- Macro for declaring new `TargetData`. -/
scoped macro (name := targetDataDecl) doc?:optional(Parser.Command.docComment)
"target_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``TargetData
  let key := WfName.quoteNameFrom id id.getId
  `($[$doc?]? family_def $id : $dty $key := $ty)

/-- Macro for declaring new `CustomData`. -/
scoped macro (name := customDataDecl) doc?:optional(Parser.Command.docComment)
"custom_data " pkg:ident tgt:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``CustomData
  let id := mkIdentFrom tgt (pkg.getId ++ tgt.getId)
  let pkg := WfName.quoteNameFrom pkg pkg.getId
  let tgt := WfName.quoteNameFrom tgt tgt.getId
  `($[$doc?]? family_def $id : $dty ($pkg, $tgt) := $ty)
