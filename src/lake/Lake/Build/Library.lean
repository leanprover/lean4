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

open System Lean

namespace Lake

/-! ## Build Lean & Static Lib -/

/--
Collect the local modules of a library.
That is, the modules from `getModuleArray` plus their local transitive imports.
-/
partial def LeanLib.recCollectLocalModules
  (self : LeanLib) : FetchM (Job (Array Module))
:= ensureJob do
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
        if mod.lib.name = self.name then
          (mods, modSet) ← go mod mods modSet
      mods := mods.push root
    return (mods, modSet)

/-- The `LibraryFacetConfig` for the builtin `modulesFacet`. -/
def LeanLib.modulesFacetConfig : LibraryFacetConfig modulesFacet :=
  mkFacetJobConfig LeanLib.recCollectLocalModules (buildable := false)

protected def LeanLib.recBuildLean
  (self : LeanLib) : FetchM (Job Unit)
:= do
  let mods ← (← self.modules.fetch).await
  mods.foldlM (init := Job.nil) fun job mod => do
    return job.mix <| ← mod.leanArts.fetch

/-- The `LibraryFacetConfig` for the builtin `leanArtsFacet`. -/
def LeanLib.leanArtsFacetConfig : LibraryFacetConfig leanArtsFacet :=
  mkFacetJobConfig LeanLib.recBuildLean

@[specialize] protected def LeanLib.recBuildStatic
  (self : LeanLib) (shouldExport : Bool) : FetchM (Job FilePath)
:= do
  let suffix :=
    if (← getIsVerbose) then
      if shouldExport then " (with exports)" else " (without exports)"
    else
      ""
  withRegisterJob s!"{self.name}:static{suffix}" do
  let mods ← (← self.modules.fetch).await
  let oJobs ← mods.flatMapM fun mod =>
    mod.nativeFacets shouldExport |>.mapM (·.fetch mod)
  let moreOJobs ← self.moreLinkObjs.mapM (·.fetchIn self.pkg)
  let libFile := if shouldExport then self.staticExportLibFile else self.staticLibFile
  /-
  Static libraries with explicit exports are built as thin libraries.
  The Lean build itself requires a thin static library with exported symbols
  as part of its build process on Windows. It does not distribute this library.
  -/
  buildStaticLib libFile (oJobs ++ moreOJobs) (thin := shouldExport)

/-- The `LibraryFacetConfig` for the builtin `staticFacet`. -/
def LeanLib.staticFacetConfig : LibraryFacetConfig staticFacet :=
  mkFacetJobConfig (LeanLib.recBuildStatic · false)

/-- The `LibraryFacetConfig` for the builtin `staticExportFacet`. -/
def LeanLib.staticExportFacetConfig : LibraryFacetConfig staticExportFacet :=
  mkFacetJobConfig (LeanLib.recBuildStatic · true)

/-! ## Build Shared Lib -/

protected def LeanLib.recBuildShared (self : LeanLib) : FetchM (Job Dynlib) := do
  withRegisterJob s!"{self.name}:shared" do
  let mods ← (← self.modules.fetch).await
  let objJobs ← mods.flatMapM fun mod =>
    mod.nativeFacets true |>.mapM (·.fetch mod)
  let objJobs ← self.moreLinkObjs.foldlM (init := objJobs)
    (·.push <$> ·.fetchIn self.pkg)
  let libJobs ← id do
    -- Fetch dependency dynlibs
    -- for situations that need them (see `Dynlib.deps`)
    let imps ← mods.foldlM (init := OrdModuleSet.empty) fun imps mod => do
      return imps.appendArray (← (← mod.transImports.fetch).await)
    let s := (NameSet.empty.insert self.name, #[])
    let (_, jobs) ← imps.foldlM (init := s) fun (libs, jobs) imp => do
      if libs.contains imp.lib.name then
        return (libs, jobs)
      else
        let jobs ← jobs.push <$> imp.lib.shared.fetch
        return (libs.insert imp.lib.name, jobs)
    let jobs ← self.moreLinkLibs.foldlM
      (·.push <$> ·.fetchIn self.pkg) jobs
    let jobs ← self.pkg.externLibs.foldlM
      (·.push <$> ·.dynlib.fetch) jobs
    return jobs
  buildLeanSharedLib self.libName self.sharedLibFile objJobs libJobs
    self.weakLinkArgs self.linkArgs (plugin := self.roots.size == 1)

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
