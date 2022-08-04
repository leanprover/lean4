/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Common

namespace Lake

/-! # Build Lean & Static Lib -/

/-- Build and collect the specified facet of the library's local modules. -/
def LeanLib.recBuildLocalModules
(facets : Array (ModuleFacet α)) (self : LeanLib) : IndexBuildM (Array α) := do
  let mut results := #[]
  let mut modSet := ModuleSet.empty
  let mods ← self.getModuleArray
  for mod in mods do
    let (_, mods) ← mod.imports.fetch
    let mods := mods.push mod
    for mod in mods do
      if self.isLocalModule mod.name then
        unless modSet.contains mod do
          for facet in facets do
            results := results.push <| ← fetch <| mod.facet facet.name
          modSet := modSet.insert mod
  return results

protected def LeanLib.recBuildLean
(self : LeanLib) : IndexBuildM (BuildJob Unit) := do
  BuildJob.mixArray (α := Unit) <| ← self.recBuildLocalModules #[Module.leanBinFacet]

/-- The `LibraryFacetConfig` for the builtin `leanFacet`. -/
def LeanLib.leanFacetConfig : LibraryFacetConfig leanFacet :=
  mkFacetJobConfig LeanLib.recBuildLean

protected def LeanLib.recBuildStatic
(self : LeanLib) : IndexBuildM (BuildJob FilePath) := do
  let oJobs ← self.recBuildLocalModules self.nativeFacets
  buildStaticLib self.staticLibFile oJobs

/-- The `LibraryFacetConfig` for the builtin `staticFacet`. -/
def LeanLib.staticFacetConfig : LibraryFacetConfig staticFacet :=
  mkFacetJobConfig LeanLib.recBuildStatic

/-! # Build Shared Lib -/

/--
Build and collect the local object files and external libraries
of a library and its modules' imports.
-/
def LeanLib.recBuildLinks
(self : LeanLib) : IndexBuildM (Array (BuildJob FilePath)) := do
  -- Build and collect modules
  let mut jobs := #[]
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty
  let mut modSet := ModuleSet.empty
  let mods ← self.getModuleArray
  for mod in mods do
    let (_, mods) ← mod.imports.fetch
    let mods := mods.push mod
    for mod in mods do
      unless modSet.contains mod do
        unless pkgSet.contains mod.pkg do
            pkgSet := pkgSet.insert mod.pkg
            pkgs := pkgs.push mod.pkg
        if self.isLocalModule mod.name then
          for facet in self.nativeFacets do
            jobs := jobs.push <| ← fetch <| mod.facet facet.name
        modSet := modSet.insert mod
  -- Build and collect external library jobs
  for pkg in pkgs do
    let externLibJobs ← pkg.externLibs.mapM (·.shared.fetch)
    for job in externLibJobs do
      jobs := jobs.push job
  return jobs

protected def LeanLib.recBuildShared
(self : LeanLib) : IndexBuildM (BuildJob FilePath) := do
  buildLeanSharedLib self.sharedLibFile (← self.recBuildLinks) self.linkArgs

/-- The `LibraryFacetConfig` for the builtin `sharedFacet`. -/
def LeanLib.sharedFacetConfig : LibraryFacetConfig sharedFacet :=
  mkFacetJobConfig LeanLib.recBuildShared

open LeanLib in
/--
A library facet name to build function map that contains builders for
the initial set of Lake package facets (e.g., `lean`, `static`, and `shared`).
-/
def initLibraryFacetConfigs : DNameMap LibraryFacetConfig :=
  DNameMap.empty
  |>.insert leanFacet leanFacetConfig
  |>.insert staticFacet staticFacetConfig
  |>.insert sharedFacet sharedFacetConfig
