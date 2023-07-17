/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Sugar
import Lake.Build.Common

open System
namespace Lake

/-- Fetch the build job of the specified package target. -/
def Package.fetchTargetJob (self : Package)
(target : Name) : IndexBuildM (Option (BuildJob Unit)) :=  do
  let some config := self.findTargetConfig? target
    | error s!"package '{self.name}' has no target '{target}'"
  return config.getJob (← fetch <| self.target target)

/-- Fetch the build result of a target. -/
protected def TargetDecl.fetch (self : TargetDecl)
[FamilyDef CustomData (self.pkg, self.name) α] : IndexBuildM α := do
  let some pkg ← findPackage? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  fetch <| pkg.target self.name

/-- Fetch the build job of the target. -/
def TargetDecl.fetchJob (self : TargetDecl) : IndexBuildM (BuildJob Unit) :=  do
  let some pkg ← findPackage? self.pkg
    | error s!"package '{self.pkg}' of target '{self.name}' does not exist in workspace"
  return self.config.getJob (← fetch <| pkg.target self.name)

/-- Fetch the build result of a package facet. -/
@[inline] protected def PackageFacetDecl.fetch (pkg : Package)
(self : PackageFacetDecl) [FamilyOut PackageData self.name α] : IndexBuildM α := do
  fetch <| pkg.facet self.name

/-- Fetch the build job of a package facet. -/
def PackageFacetConfig.fetchJob (pkg : Package)
(self : PackageFacetConfig name) : IndexBuildM (BuildJob Unit) :=  do
  let some getJob := self.getJob?
    | error "package facet '{pkg.name}' has no associated build job"
  return getJob <| ← fetch <| pkg.facet self.name

/-- Fetch the build job of a library facet. -/
def Package.fetchFacetJob
(name : Name) (self : Package) : IndexBuildM (BuildJob Unit) :=  do
  let some config := (← getWorkspace).packageFacetConfigs.find? name
    | error "package facet '{name}' does not exist in workspace"
  inline <| config.fetchJob self

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
Build the `extraDepTarget` for the package and its transitive dependencies.
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
    if let some config := self.findTargetConfig? target then
      job ← job.mix <| config.getJob <| ← fetch <| self.target target
    else
      error s!"unknown target `{target}`"
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
