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
open Lean (Name NameMap)

/-- A monad equipped with a Lake build store. -/
abbrev MonadBuildStore (m) := MonadDStore BuildKey BuildData m

/-- The type of the Lake build store. -/
abbrev BuildStore :=
  DRBMap BuildKey BuildData BuildKey.quickCmp

@[inline] def BuildStore.empty : BuildStore := DRBMap.empty

namespace BuildStore

-- Linter reports false positives on the `v` variables below
set_option linter.unusedVariables false

/-- Derive an array of built module facets from the store. -/
def collectModuleFacetArray (self : BuildStore)
(facet : Name) [FamilyOut ModuleData facet α] : Array α := Id.run do
  let mut res : Array α := #[]
  for ⟨k, v⟩ in self do
    match k with
    | .moduleFacet m f =>
      if h : f = facet then
        have of_data := by unfold BuildData; simp [h]
        res := res.push <| cast of_data v
    | _ => pure ()
  return res

/-- Derive a map of module names to built facets from the store. -/
def collectModuleFacetMap (self : BuildStore)
(facet : Name) [FamilyOut ModuleData facet α] : NameMap α := Id.run do
  let mut res := Lean.mkNameMap α
  for ⟨k, v⟩ in self do
    match k with
    | .moduleFacet m f =>
      if h : f = facet then
        have of_data := by unfold BuildData; simp [h]
        res := res.insert m <| cast of_data v
    | _ => pure ()
  return res

/-- Derive an array of built package facets from the store. -/
def collectPackageFacetArray (self : BuildStore)
(facet : Name) [FamilyOut PackageData facet α] : Array α := Id.run do
  let mut res : Array α := #[]
  for ⟨k, v⟩ in self do
    match k with
    | .packageFacet _ f =>
      if h : f = facet then
        have of_data := by unfold BuildData; simp [h]
        res := res.push <| cast of_data v
    | _ => pure ()
  return res

/-- Derive an array of built target facets from the store. -/
def collectTargetFacetArray (self : BuildStore)
(facet : Name) [FamilyOut TargetData facet α] : Array α := Id.run do
  let mut res : Array α := #[]
  for ⟨k, v⟩ in self do
    match k with
    | .targetFacet _ _ f =>
      if h : f = facet then
        have of_data := by unfold BuildData; simp [h]
        res := res.push <| cast of_data v
    | _ => pure ()
  return res

/-- Derive an array of built external shared libraries from the store. -/
def collectSharedExternLibs (self : BuildStore)
[FamilyOut TargetData `externLib.shared α] : Array α :=
  self.collectTargetFacetArray `externLib.shared
