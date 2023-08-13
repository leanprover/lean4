/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Sugar
import Lake.Build.Common
import Lake.Build.Targets

/-! # Package Facet Builds
Build function definitions for a package's builtin facets.
-/

open System
namespace Lake

/-- Compute a topological ordering of the package's transitive dependencies. -/
def Package.recComputeDeps (self : Package) : IndexBuildM (Array Package) := do
  let mut deps := #[]
  let mut depSet := PackageSet.empty
  for dep in self.deps do
    for depDep in (← fetch <| dep.facet `deps) do
      unless depSet.contains depDep do
        deps := deps.push depDep
        depSet := depSet.insert depDep
    unless depSet.contains dep do
      deps := deps.push dep
      depSet := depSet.insert dep
  return deps

/-- The `PackageFacetConfig` for the builtin `depsFacet`. -/
def Package.depsFacetConfig : PackageFacetConfig depsFacet :=
  mkFacetConfig Package.recComputeDeps

/--
Build the `extraDepTargets` for the package and its transitive dependencies.
Also fetch pre-built releases for the package's' dependencies.
-/
def Package.recBuildExtraDepTargets (self : Package) : IndexBuildM (BuildJob Unit) := do
  let mut job := BuildJob.nil
  -- Build dependencies' extra dep targets
  for dep in self.deps do
    job ← job.mix <| ← dep.extraDep.fetch
  -- Fetch pre-built release if desired and this package is a dependency
  if self.name ≠ (← getWorkspace).root.name ∧ self.preferReleaseBuild then
    job ← job.mix <| ← self.release.fetch
  -- Build this package's extra dep targets
  for target in self.extraDepTargets do
    job ← job.mix <| ← self.fetchTargetJob target
  return job

/-- The `PackageFacetConfig` for the builtin `dynlibFacet`. -/
def Package.extraDepFacetConfig : PackageFacetConfig extraDepFacet :=
  mkFacetJobConfigSmall Package.recBuildExtraDepTargets

/-- Download and unpack the package's prebuilt release archive (from GitHub). -/
def Package.fetchRelease (self : Package) : SchedulerM (BuildJob Unit) := Job.async do
  let some (repoUrl, tag) := self.release? | do
    logWarning "wanted prebuilt release, but release repository and tag was not known"
    return ((), .nil)
  let url := s!"{repoUrl}/releases/download/{tag}/{self.buildArchive}"
  let logName := s!"{self.name}/{tag}/{self.buildArchive}"
  try
    let depTrace := Hash.ofString url
    let trace ← buildFileUnlessUpToDate self.buildArchiveFile depTrace do
      download logName url self.buildArchiveFile
      untar logName self.buildArchiveFile self.buildDir
    return ((), trace)
  else
    return ((), .nil)

/-- The `PackageFacetConfig` for the builtin `releaseFacet`. -/
def Package.releaseFacetConfig : PackageFacetConfig releaseFacet :=
  mkFacetJobConfig (·.fetchRelease)

open Package in
/--
A package facet name to build function map that contains builders for
the initial set of Lake package facets (e.g., `extraDep`).
-/
def initPackageFacetConfigs : DNameMap PackageFacetConfig :=
  DNameMap.empty
  |>.insert depsFacet depsFacetConfig
  |>.insert extraDepFacet extraDepFacetConfig
  |>.insert releaseFacet releaseFacetConfig
