/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Common
import Lake.Build.Targets

/-! # Library Facet Builds
Build function definitions for a library's builtin facets.
-/

namespace Lake
open System (FilePath)

/-! ## Build Lean & Static Lib -/

/--
Collect the local modules of a library.
That is, the modules from `getModuleArray` plus their local transitive imports.
-/
partial def LeanLib.recCollectLocalModules (self : LeanLib) : FetchM (Array Module) := do
  let mut mods := #[]
  let mut modSet := ModuleSet.empty
  for mod in (← self.getModuleArray) do
    (mods, modSet) ← go mod mods modSet
  return mods
where
  go root mods modSet := do
    let mut mods := mods
    let mut modSet := modSet
    unless modSet.contains root do
      modSet := modSet.insert root
      let imps ← root.imports.fetch
      for mod in imps do
        if self.isLocalModule mod.name then
          (mods, modSet) ← go mod mods modSet
      mods := mods.push root
    return (mods, modSet)

/-- The `LibraryFacetConfig` for the builtin `modulesFacet`. -/
def LeanLib.modulesFacetConfig : LibraryFacetConfig modulesFacet :=
  mkFacetConfig LeanLib.recCollectLocalModules

protected def LeanLib.recBuildLean
(self : LeanLib) : FetchM (BuildJob Unit) := do
  let mods ← self.modules.fetch
  mods.foldlM (init := BuildJob.nil) fun job mod => do
    return job.mix <| ← mod.leanArts.fetch

/-- The `LibraryFacetConfig` for the builtin `leanArtsFacet`. -/
def LeanLib.leanArtsFacetConfig : LibraryFacetConfig leanArtsFacet :=
  mkFacetJobConfig LeanLib.recBuildLean

@[specialize] protected def LeanLib.recBuildStatic
(self : LeanLib) (shouldExport : Bool) : FetchM (BuildJob FilePath) := do
  let suffix :=
    if (← getIsVerbose) then
      if shouldExport then " (with exports)" else " (without exports)"
    else
      ""
  withRegisterJob s!"{self.name}:static{suffix}" do
  let mods ← self.modules.fetch
  let oJobs ← mods.flatMapM fun mod =>
    mod.nativeFacets shouldExport |>.mapM fun facet => fetch <| mod.facet facet.name
  let libFile := if shouldExport then self.staticExportLibFile else self.staticLibFile
  buildStaticLib libFile oJobs

/-- The `LibraryFacetConfig` for the builtin `staticFacet`. -/
def LeanLib.staticFacetConfig : LibraryFacetConfig staticFacet :=
  mkFacetJobConfig (LeanLib.recBuildStatic · false)

/-- The `LibraryFacetConfig` for the builtin `staticExportFacet`. -/
def LeanLib.staticExportFacetConfig : LibraryFacetConfig staticExportFacet :=
  mkFacetJobConfig (LeanLib.recBuildStatic · true)


/-! ## Build Shared Lib -/

protected def LeanLib.recBuildShared
(self : LeanLib) : FetchM (BuildJob FilePath) := do
  withRegisterJob s!"{self.name}:shared" do
  let mods ← self.modules.fetch
  let oJobs ← mods.flatMapM fun mod =>
    mod.nativeFacets true |>.mapM fun facet => fetch <| mod.facet facet.name
  let pkgs := mods.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
  let externJobs ← pkgs.flatMapM (·.externLibs.mapM (·.shared.fetch))
  buildLeanSharedLib self.sharedLibFile (oJobs ++ externJobs) self.weakLinkArgs self.linkArgs

/-- The `LibraryFacetConfig` for the builtin `sharedFacet`. -/
def LeanLib.sharedFacetConfig : LibraryFacetConfig sharedFacet :=
  mkFacetJobConfig LeanLib.recBuildShared

/-! ## Build `extraDepTargets` -/

/-- Build the `extraDepTargets` for the library and its package. -/
def LeanLib.recBuildExtraDepTargets (self : LeanLib) : FetchM (BuildJob Unit) := do
  self.extraDepTargets.foldlM (init := ← self.pkg.extraDep.fetch) fun job target => do
    return job.mix <| ← self.pkg.fetchTargetJob target

/-- The `LibraryFacetConfig` for the builtin `extraDepFacet`. -/
def LeanLib.extraDepFacetConfig : LibraryFacetConfig extraDepFacet :=
  mkFacetJobConfig LeanLib.recBuildExtraDepTargets

open LeanLib in
/--
A library facet name to build function map that contains builders for
the initial set of Lake library facets (e.g., `lean`, `static`, and `shared`).
-/
def initLibraryFacetConfigs : DNameMap LibraryFacetConfig :=
  DNameMap.empty
  |>.insert modulesFacet modulesFacetConfig
  |>.insert leanArtsFacet leanArtsFacetConfig
  |>.insert staticFacet staticFacetConfig
  |>.insert staticExportFacet staticExportFacetConfig
  |>.insert sharedFacet sharedFacetConfig
  |>.insert extraDepFacet extraDepFacetConfig
