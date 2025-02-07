/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Common
import Lake.Build.Targets
import Lake.Build.Topological

/-! # Library Facet Builds
Build function definitions for a library's builtin facets.
-/

open System Lean

namespace Lake

/-! ## Build Lean & Static Lib -/
/--
Collect the local modules of a library.
That is, the modules from `getModuleArray` plus their local transitive imports.
-/
def LeanLib.recCollectLocalModules
  (self : LeanLib) : FetchM (Job (Array Module))
:= ensureJob do
  let jobs ← (← self.getModuleArray).mapM go
  let job : Job OrdModuleSet := jobs.foldl (init := .pure .empty) fun r job =>
    r.zipWith (sync := true) (·.appendArray ·) job
  return job.map (sync := true) (·.toArray)
where
  go root : FetchM (Job (Array Module)) :=
    have : MonadCycleOf Name (CallStackT Name FetchM) :=
      {throwCycle cycle := error s!"import cycle detected:\n{formatCycle cycle}"}
    CallStackT.run (κ := Name) do recFetchAcyclic Module.name recFetch root
  recFetch root recurse := fun stack => do
    (← root.imports.fetch).bindM fun imps => do
    let jobs ← imps.foldlM (init := #[]) fun jobs imp => do
        if self.isLocalModule imp.name then
          return jobs.push (← recurse imp stack)
        else
          return jobs
    let job : Job OrdModuleSet := jobs.foldl (init := .pure .empty) fun r job =>
      r.zipWith (sync := true) (·.appendArray ·) job
    return job.map (sync := true) (·.toArray.push root)

/-- The `LibraryFacetConfig` for the builtin `modulesFacet`. -/
def LeanLib.modulesFacetConfig : LibraryFacetConfig modulesFacet :=
  mkFacetJobConfig LeanLib.recCollectLocalModules (buildable := false)

protected def LeanLib.recBuildLean (self : LeanLib) : FetchM (Job Unit) := do
  (← self.modules.fetch).bindM fun mods =>
    mods.foldlM (init := Job.nil) fun job mod => do
      return job.mix <| ← mod.leanArts.fetch

/-- The `LibraryFacetConfig` for the builtin `leanArtsFacet`. -/
def LeanLib.leanArtsFacetConfig : LibraryFacetConfig leanArtsFacet :=
  mkFacetJobConfig LeanLib.recBuildLean

protected def LeanLib.recBuildStatic
  (self : LeanLib) (shouldExport : Bool)
: FetchM (Job FilePath) := do
  let suffix :=
    if (← getIsVerbose) then
      if shouldExport then " (with exports)" else " (without exports)"
    else
      ""
  withRegisterJob s!"{self.name}:static{suffix}" do
  (← self.modules.fetch).bindM fun mods => do
  let oJobs ← mods.flatMapM fun mod =>
    mod.nativeFacets shouldExport |>.mapM fun facet => fetch <| mod.facet facet.name
  let libFile := if shouldExport then self.staticExportLibFile else self.staticLibFile
  buildStaticLib libFile oJobs

/-- The `LibraryFacetConfig` for the builtin `staticFacet`. -/
def LeanLib.staticFacetConfig : LibraryFacetConfig staticFacet :=
  mkFacetJobConfig (inline <| LeanLib.recBuildStatic · false)

/-- The `LibraryFacetConfig` for the builtin `staticExportFacet`. -/
def LeanLib.staticExportFacetConfig : LibraryFacetConfig staticExportFacet :=
  mkFacetJobConfig (inline <| LeanLib.recBuildStatic · true)

/-! ## Build Shared Lib -/

protected def LeanLib.recBuildShared (self : LeanLib) : FetchM (Job FilePath) := do
  withRegisterJob s!"{self.name}:shared" do
  (← self.modules.fetch).bindM fun mods => do
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
def LeanLib.recBuildExtraDepTargets (self : LeanLib) : FetchM (Job Unit) := do
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
