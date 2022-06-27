/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Data
import Lake.Util.StoreInsts

/-!
# The Lake Build Store

The Lake build store is the map of Lake build keys to build task and/or
build results that is slowly filled during a recursive build (e.g., via
topological-based build of an initial key's dependencies).
-/

namespace Lake

/-! ## Abstract Monad -/

/-- A monad equipped with a Lake build store. -/
abbrev MonadBuildStore (m) := MonadDStore BuildKey BuildData m

@[inline] instance [MonadBuildStore m]
[DynamicType ModuleData f α] : MonadStore (ModuleBuildKey f) α m where
  fetch? k := fetch? k.toBuildKey
  store k a := store k.toBuildKey a

@[inline] instance [MonadBuildStore m]
[DynamicType PackageData f α] : MonadStore (PackageBuildKey f) α m where
  fetch? k := fetch? k.toBuildKey
  store k a := store k.toBuildKey a

/-! ## Concrete Type -/

/-- The type of the Lake build store. -/
abbrev BuildStore :=
  DRBMap BuildKey BuildData BuildKey.quickCmp

@[inline] def BuildStore.empty : BuildStore := DRBMap.empty

namespace BuildStore

/-- Derive an array of built module facets from the store. -/
def collectModuleFacetArray (self : BuildStore)
(facet : WfName) [DynamicType ModuleData facet α] : Array α := Id.run do
  let mut res : Array α := #[]
  for ⟨k, v⟩ in self do
    if h : k.isModuleKey ∧ k.facet = facet then
      let of_data := by unfold BuildData; simp [h, eq_dynamic_type]
      res := res.push <| cast of_data v
  return res

/-- Derive a map of module names to built facets from the store. -/
def collectModuleFacetMap (self : BuildStore)
(facet : WfName) [DynamicType ModuleData facet α] : NameMap α := Id.run do
  let mut res := Lean.mkNameMap α
  for ⟨k, v⟩ in self do
    if h : k.isModuleKey ∧ k.facet = facet then
      let of_data := by simp [isModuleKey_data h.1, h.2, eq_dynamic_type]
      res := res.insert (k.module h.1) <| cast of_data v
  return res

/-- Derive an array of built module facets from the store. -/
def collectPackageFacetArray (self : BuildStore)
(facet : WfName) [DynamicType PackageData facet α] : Array α := Id.run do
  let mut res : Array α := #[]
  for ⟨k, v⟩ in self do
    if h : k.isPackageKey ∧ k.facet = facet then
      let of_data := by simp [isPackageKey_data h.1, h.2, eq_dynamic_type]
      res := res.push <| cast of_data v
  return res

/-- Derive an array of built external shared libraries from the store. -/
def collectSharedExternLibs (self : BuildStore)
[DynamicType TargetData &`externLib.shared α] : Array α := Id.run do
  let mut res : Array α := #[]
  for ⟨k, v⟩ in self do
    if h : k.isTargetKey ∧ k.facet = &`externLib.shared then
      let of_data := by simp [isTargetKey_data h.1, h.2, eq_dynamic_type]
      res := res.push <| cast of_data v
  return res
