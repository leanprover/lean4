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

--------------------------------------------------------------------------------
/-! ## Build Data                                                             -/
--------------------------------------------------------------------------------

/--
Type of the build data associated with a key in the Lake build store.
It is dynamic type composed of the three separate dynamic types for modules,
packages, and targets.
-/
abbrev BuildData (key : BuildKey) :=
  if key.isModuleKey then
    ModuleData key.facet
  else if key.isPackageKey then
    PackageData key.facet
  else
    TargetData key.facet

theorem isModuleKey_data {k : BuildKey}
(h : k.isModuleKey = true) : BuildData k = ModuleData k.facet := by
  unfold BuildData; simp [h]

instance (k : ModuleBuildKey f)
[t : DynamicType ModuleData f α] : DynamicType BuildData k α where
  eq_dynamic_type := by
    have h := isModuleKey_data k.is_module_key
    simp [h, k.facet_eq_fixed, t.eq_dynamic_type]

theorem isPackageKey_data {k : BuildKey}
(h : k.isPackageKey = true) : BuildData k = PackageData k.facet := by
  unfold BuildData, BuildKey.isModuleKey
  simp [of_decide_eq_true (of_decide_eq_true h |>.1), h]

instance (k : PackageBuildKey f)
[t : DynamicType PackageData f α] : DynamicType BuildData k α where
  eq_dynamic_type := by
    have h := isPackageKey_data k.is_package_key
    simp [h, k.facet_eq_fixed, t.eq_dynamic_type]

theorem isTargetKey_data {k : BuildKey}
(h : k.isTargetKey = true) : BuildData k = TargetData k.facet := by
  unfold BuildData, BuildKey.isModuleKey, BuildKey.isPackageKey
  have ⟨has_p, has_t⟩ := of_decide_eq_true h
  simp [of_decide_eq_true has_p, of_decide_eq_true has_t, h]

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
