/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Key
import Lake.Util.DynamicType

open Lean
namespace Lake

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
opaque TargetData (key : BuildKey) : Type

/--
Type of the build data associated with a key in the Lake build store.
It is dynamic type composed of the three separate dynamic types for modules,
packages, and targets.
-/
def BuildData (key : BuildKey) :=
  if key.isModuleKey then
    ModuleData key.facet
  else if key.isPackageKey then
    PackageData key.facet
  else
    TargetData key

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
