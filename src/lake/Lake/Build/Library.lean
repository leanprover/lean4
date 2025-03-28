/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Common
import Lake.Build.Targets
import Lake.Build.Target.Fetch

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
partial def LeanLib.recCollectLocalModules (self : LeanLib) : FetchM (Job (Array Module)) := ensureJob do
  let mut mods := #[]
  let mut modSet := ModuleSet.empty
  for mod in (← self.getModuleArray) do
    (mods, modSet) ← go mod mods modSet
  return Job.pure mods
where
  go root mods modSet := do
    let mut mods := mods
    let mut modSet := modSet
    unless modSet.contains root do
      modSet := modSet.insert root
      let imps ← (← root.imports.fetch).await
      for mod in imps do
        if self.isLocalModule mod.name then
          (mods, modSet) ← go mod mods modSet
      mods := mods.push root
    return (mods, modSet)

/-- The `LibraryFacetConfig` for the builtin `modulesFacet`. -/
def LeanLib.modulesFacetConfig : LibraryFacetConfig modulesFacet :=
  mkFacetJobConfig LeanLib.recCollectLocalModules (buildable := false)

protected def LeanLib.recBuildLean
(self : LeanLib) : FetchM (Job Unit) := do
  let mods ← (← self.modules.fetch).await
  mods.foldlM (init := Job.nil) fun job mod => do
    return job.mix <| ← mod.leanArts.fetch

/-- The `LibraryFacetConfig` for the builtin `leanArtsFacet`. -/
def LeanLib.leanArtsFacetConfig : LibraryFacetConfig leanArtsFacet :=
  mkFacetJobConfig LeanLib.recBuildLean

@[specialize] protected def LeanLib.recBuildStatic
(self : LeanLib) (shouldExport : Bool) : FetchM (Job FilePath) := do
  let suffix :=
    if (← getIsVerbose) then
      if shouldExport then " (with exports)" else " (without exports)"
    else
      ""
  withRegisterJob s!"{self.name}:static{suffix}" do
  let mods ← (← self.modules.fetch).await
  let oJobs ← mods.flatMapM fun mod =>
    mod.nativeFacets shouldExport |>.mapM (·.fetch mod)
  let libFile := if shouldExport then self.staticExportLibFile else self.staticLibFile
  /-
  Static libraries with explicit exports are built as thin libraries.
  The Lean build itself requires a thin static library with exported symbols
  as part of its build process on Windows. It does not distribute this library.
  -/
  buildStaticLib libFile oJobs (thin := shouldExport)

/-- The `LibraryFacetConfig` for the builtin `staticFacet`. -/
def LeanLib.staticFacetConfig : LibraryFacetConfig staticFacet :=
  mkFacetJobConfig (LeanLib.recBuildStatic · false)

/-- The `LibraryFacetConfig` for the builtin `staticExportFacet`. -/
def LeanLib.staticExportFacetConfig : LibraryFacetConfig staticExportFacet :=
  mkFacetJobConfig (LeanLib.recBuildStatic · true)

/-! ## Build Shared Lib -/

protected def LeanLib.recBuildShared
(self : LeanLib) : FetchM (Job FilePath) := do
  withRegisterJob s!"{self.name}:shared" do
  let mods ← (← self.modules.fetch).await
  let oJobs ← mods.flatMapM fun mod =>
    mod.nativeFacets true |>.mapM (·.fetch mod)
  let pkgs := mods.foldl (·.insert ·.pkg) OrdPackageSet.empty |>.toArray
  let externJobs ← pkgs.flatMapM (·.externLibs.mapM (·.shared.fetch))
  buildLeanSharedLib self.sharedLibFile (oJobs ++ externJobs) self.weakLinkArgs self.linkArgs

/-- The `LibraryFacetConfig` for the builtin `sharedFacet`. -/
def LeanLib.sharedFacetConfig : LibraryFacetConfig sharedFacet :=
  mkFacetJobConfig LeanLib.recBuildShared

/-! ## Other -/

/--
Build extra target dependencies of the library (e.g., `extraDepTargets`, `needs`). -/
def LeanLib.recBuildExtraDepTargets (self : LeanLib) : FetchM (Job Unit) := do
  let job ← self.extraDepTargets.foldlM (init := ← self.pkg.extraDep.fetch) fun job target => do
    return job.mix <| ← self.pkg.fetchTargetJob target
  let job ← self.config.needs.foldlM (init := job) fun job key => do
    return job.mix <| ← key.fetchIn self.pkg
  return job

/-- The `LibraryFacetConfig` for the builtin `extraDepFacet`. -/
def LeanLib.extraDepFacetConfig : LibraryFacetConfig extraDepFacet :=
  mkFacetJobConfig LeanLib.recBuildExtraDepTargets

/-- Build the default facets for the library. -/
def LeanLib.recBuildDefaultFacets (self : LeanLib) : FetchM (Job Unit) := do
  Job.mixArray <$> self.defaultFacets.mapM fun facet => do
    let job ← (self.facetCore facet).fetch
    return job.toOpaque

/-- The `LibraryFacetConfig` for the builtin `defaultFacet`. -/
def LeanLib.defaultFacetConfig : LibraryFacetConfig defaultFacet :=
  mkFacetJobConfig LeanLib.recBuildDefaultFacets

/--
A name-configuration map for the initial set of
Lean library facets (e.g., `lean`, `static`, `shared`).
-/
def LeanLib.initFacetConfigs : DNameMap LeanLibFacetConfig :=
  DNameMap.empty
  |>.insert defaultFacet defaultFacetConfig
  |>.insert modulesFacet modulesFacetConfig
  |>.insert leanArtsFacet leanArtsFacetConfig
  |>.insert staticFacet staticFacetConfig
  |>.insert staticExportFacet staticExportFacetConfig
  |>.insert sharedFacet sharedFacetConfig
  |>.insert extraDepFacet extraDepFacetConfig

@[inherit_doc LeanLib.initFacetConfigs]
abbrev initLibraryFacetConfigs : DNameMap LibraryFacetConfig :=
  LeanLib.initFacetConfigs
