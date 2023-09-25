/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Git
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
  (·.toArray) <$> self.deps.foldlM (init := OrdPackageSet.empty) fun deps dep => do
    return (← fetch <| dep.facet `deps).foldl (·.insert ·) deps |>.insert dep

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
  let repo := GitRepo.mk self.dir
  let repoUrl? := self.releaseRepo? <|> self.remoteUrl?
  let some repoUrl := repoUrl? <|> (← repo.getFilteredRemoteUrl?) | do
    logWarning <| s!"{self.name}: wanted prebuilt release, " ++
      "but package's repository URL was not known; it may need to set `releaseRepo?`"
    return ((), .nil)
  let some tag ← repo.findTag? | do
    logWarning <| s!"{self.name}: wanted prebuilt release, " ++
      "but could not find an associated tag for the package's revision"
    return ((), .nil)
  let url := s!"{repoUrl}/releases/download/{tag}/{self.buildArchive}"
  let logName := s!"{self.name}/{tag}/{self.buildArchive}"
  try
    let depTrace := Hash.ofString url
    let traceFile := FilePath.mk <| self.buildArchiveFile.toString ++ ".trace"
    buildUnlessUpToDate self.buildArchiveFile depTrace traceFile do
      logStep s!"Fetching {self.name} cloud release"
      download logName url self.buildArchiveFile
      untar logName self.buildArchiveFile self.buildDir
    return ((), .nil)
  else
    return ((), .nil)

/-- The `PackageFacetConfig` for the builtin `releaseFacet`. -/
def Package.releaseFacetConfig : PackageFacetConfig releaseFacet :=
  mkFacetJobConfig (·.fetchRelease)

/-- Perform a build job after first checking for a cloud release for the package. -/
def Package.afterReleaseAsync (self : Package) (build : SchedulerM (Job α)) : IndexBuildM (Job α) := do
  if self.preferReleaseBuild ∧ self.name ≠ (← getRootPackage).name then
    (← self.release.fetch).bindAsync fun _ _ => build
  else
    build

/-- Perform a build after first checking for a cloud release for the package. -/
def Package.afterReleaseSync (self : Package) (build : BuildM α) : IndexBuildM (Job α) := do
  if self.preferReleaseBuild ∧ self.name ≠ (← getRootPackage).name then
    (← self.release.fetch).bindSync fun _ _ => build
  else
    Job.async build

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
