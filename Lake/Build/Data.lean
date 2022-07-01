/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Key
import Lake.Util.DynamicType

open Lean
namespace Lake

--------------------------------------------------------------------------------
/-! ## Build Data Subtypes                                                    -/
--------------------------------------------------------------------------------

/--
Type of build data associated with a module facet in the Lake build store.
For example a transitive × direct import pair for `imports` or an active build
target for `lean.c`.

It is a dynamic type, meaning additional alternatives can be add lazily
as needed.
-/
opaque ModuleData (facet : WfName) : Type

/-- Type of build data associated with package facets (e.g., `extraDep`). -/
opaque PackageData (facet : WfName) : Type

/-- Type of build data associated with Lake targets (e.g., `extern_lib`). -/
opaque TargetData (facet : WfName) : Type

/-- Type of build data associated with custom targets. -/
opaque CustomData (target : WfName) : Type

--------------------------------------------------------------------------------
/-! ## Build Data                                                             -/
--------------------------------------------------------------------------------

/--
Type of the build data associated with a key in the Lake build store.
It is dynamic type composed of the three separate dynamic types for modules,
packages, and targets.
-/
abbrev BuildData : BuildKey → Type
| .moduleFacet _ f => ModuleData f
| .packageFacet _ f => PackageData f
| .targetFacet _ _ f => TargetData f
| .customTarget _ t => CustomData t

--------------------------------------------------------------------------------
/-! ## Macros for Declaring Build Data                                        -/
--------------------------------------------------------------------------------

/-- Macro for declaring new `PackageData`. -/
scoped macro (name := packageDataDecl) doc?:optional(Parser.Command.docComment)
"package_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``PackageData
  let key := WfName.quoteFrom id <| WfName.ofName <| id.getId
  `($[$doc?]? dynamic_data $id : $dty $key := $ty)

/-- Macro for declaring new `ModuleData`. -/
scoped macro (name := moduleDataDecl) doc?:optional(Parser.Command.docComment)
"module_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``ModuleData
  let key := WfName.quoteFrom id <| WfName.ofName <| id.getId
  `($[$doc?]? dynamic_data $id : $dty $key := $ty)

/-- Macro for declaring new `TargetData`. -/
scoped macro (name := targetDataDecl) doc?:optional(Parser.Command.docComment)
"target_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``TargetData
  let key := WfName.quoteFrom id <| WfName.ofName <| id.getId
  `($[$doc?]? dynamic_data $id : $dty $key := $ty)

/-- Macro for declaring new `CustomData`. -/
scoped macro (name := customDataDecl) doc?:optional(Parser.Command.docComment)
"custom_data " id:ident " : " ty:term : command => do
  let dty := mkCIdentFrom (← getRef) ``CustomData
  let key := WfName.quoteFrom id <| WfName.ofName <| id.getId
  `($[$doc?]? dynamic_data $id : $dty $key := $ty)
