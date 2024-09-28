/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Git
import Lake.Util.Sugar
import Lake.Build.Common
import Lake.Build.Targets
import Lake.Reservoir

/-! # Package Facet Builds
Build function definitions for a package's builtin facets.
-/

open System
namespace Lake

/-- Compute a topological ordering of the package's transitive dependencies. -/
def Package.recComputeDeps (self : Package) : FetchM (Array Package) := do
  (·.toArray) <$> self.deps.foldlM (init := OrdPackageSet.empty) fun deps dep => do
    return (← fetch <| dep.facet `deps).foldl (·.insert ·) deps |>.insert dep

/-- The `PackageFacetConfig` for the builtin `depsFacet`. -/
def Package.depsFacetConfig : PackageFacetConfig depsFacet :=
  mkFacetConfig Package.recComputeDeps

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub).
-/
def Package.fetchOptBuildCache (self : Package) := do
  if self.preferReleaseBuild then
    self.optRelease.fetch
  else
    self.optBarrel.fetch

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub). Prints a warning on failure.
-/
def Package.fetchOptBuildCacheWithWarning (self : Package) := do
  let job ← self.fetchOptBuildCache
  job.bindSync fun success t => do
    unless success do
      let facet := if self.preferReleaseBuild then optReleaseFacet else optBarrelFacet
      logWarning s!"building from source; \
        failed to fetch cloud release (see '{self.name}:{facet}' for details)"
    return ((), t)

@[deprecated fetchOptBuildCacheWithWarning (since := "2024-09-27")]
def Package.fetchOptRelease := @fetchOptBuildCacheWithWarning

/--
Build the `extraDepTargets` for the package and its transitive dependencies.
Also fetch pre-built releases for the package's' dependencies.
-/
def Package.recBuildExtraDepTargets (self : Package) : FetchM (BuildJob Unit) :=
  withRegisterJob s!"{self.name}:extraDep" do
  let mut job := BuildJob.nil
  -- Build dependencies' extra dep targets
  for dep in self.deps do
    job := job.mix <| ← dep.extraDep.fetch
  -- Fetch build cache if this package is a dependency
  if self.name ≠ (← getWorkspace).root.name then
    job := job.add <| ← self.fetchOptBuildCacheWithWarning
  -- Build this package's extra dep targets
  for target in self.extraDepTargets do
    job := job.mix <| ← self.fetchTargetJob target
  return job

/-- The `PackageFacetConfig` for the builtin `dynlibFacet`. -/
def Package.extraDepFacetConfig : PackageFacetConfig extraDepFacet :=
  mkFacetJobConfig Package.recBuildExtraDepTargets

/-- Compute the package's Reservoir barrel URL. -/
def Package.getBarrelUrl (self : Package) : JobM String := do
  if self.scope.isEmpty then
    error "package has no Reservoir scope"
  let repo := GitRepo.mk self.dir
  let some rev ← repo.getHeadRevision?
    | error "failed to resolve HEAD revision"
  let pkgName := self.name.toString (escape := false)
  let baseUrl := Reservoir.pkgApiUrl (← getLakeEnv) self.scope pkgName
  return s!"{baseUrl}/barrels/{rev}?dev"

/-- Compute the package's GitHub release URL. -/
def Package.getReleaseUrl (self : Package) : JobM String := do
  let repo := GitRepo.mk self.dir
  let repoUrl? := self.releaseRepo? <|> self.remoteUrl?
  let some repoUrl := repoUrl? <|> (← repo.getFilteredRemoteUrl?)
    | error "release repository URL not known; \
        the package may need to set 'releaseRepo'"
  let some tag ← repo.findTag?
    | let rev ← if let some rev ← repo.getHeadRevision? then pure s!" '{rev}'" else pure ""
      error s!"no release tag found for revision{rev}"
  return s!"{repoUrl}/releases/download/{tag}/{self.buildArchive}"

/-- Tries to download and unpack a build archive for the package from a URL. -/
def Package.fetchBuildArchive (self : Package) (url : String) (archiveFile : FilePath) : JobM PUnit := do
  let depTrace := Hash.ofString url
  let traceFile := archiveFile.addExtension "trace"
  let upToDate ← buildUnlessUpToDate? (action := .fetch) archiveFile depTrace traceFile do
    download url archiveFile
  unless upToDate && (← self.buildDir.pathExists) do
    updateAction .fetch
    untar archiveFile self.buildDir

@[inline]
private def Package.mkOptBuildArchiveFacetConfig
  {facet : Name} (getUrl : Package → JobM String)
  [FamilyDef PackageData facet (BuildJob Bool)]
: PackageFacetConfig facet := mkFacetJobConfig fun pkg =>
  withRegisterJob s!"{pkg.name}:{facet}" (optional := true) <| Job.async do
  try
    let url ← getUrl pkg
    pkg.fetchBuildArchive url pkg.barrelFile
    return (true, .nil)
  catch _ =>
    updateAction .fetch
    return (false, .nil)

@[inline]
private def Package.mkBuildArchiveFacetConfig
  {facet : Name} (optFacet : Name) (what : String)
  [FamilyDef PackageData facet (BuildJob Unit)]
  [FamilyDef PackageData optFacet (BuildJob Bool)]
: PackageFacetConfig facet :=
  mkFacetJobConfig fun pkg =>
    withRegisterJob s!"{pkg.name}:{facet}" do
      (← fetch <| pkg.facet optFacet).bindSync fun success t => do
        unless success do
          error s!"failed to fetch {what} (see '{pkg.name}:{optFacet}' for details)"
        return ((), t)

/-- The `PackageFacetConfig` for the builtin `optReleaseFacet`. -/
def Package.optCacheFacetConfig : PackageFacetConfig optCacheFacet :=
  mkFacetJobConfig (·.fetchOptBuildCache)

/-- The `PackageFacetConfig` for the builtin `barrelFacet`. -/
def Package.cacheFacetConfig : PackageFacetConfig cacheFacet :=
  mkBuildArchiveFacetConfig optCacheFacet "build cache"

/-- The `PackageFacetConfig` for the builtin `optReleaseFacet`. -/
def Package.optBarrelFacetConfig : PackageFacetConfig optBarrelFacet :=
  mkOptBuildArchiveFacetConfig getBarrelUrl

/-- The `PackageFacetConfig` for the builtin `barrelFacet`. -/
def Package.barrelFacetConfig : PackageFacetConfig barrelFacet :=
  mkBuildArchiveFacetConfig optBarrelFacet "Reservoir barrel"

/-- The `PackageFacetConfig` for the builtin `optReleaseFacet`. -/
def Package.optReleaseFacetConfig : PackageFacetConfig optReleaseFacet :=
  mkOptBuildArchiveFacetConfig getReleaseUrl

/-- The `PackageFacetConfig` for the builtin `releaseFacet`. -/
def Package.releaseFacetConfig : PackageFacetConfig releaseFacet :=
  mkBuildArchiveFacetConfig optReleaseFacet "GitHub release"

/--
Perform a build job after first checking for an (optional) cloud build
for the package (e.g., from Reservoir or GitHub).
-/
def Package.afterBuildCacheAsync (self : Package) (build : SpawnM (Job α)) : FetchM (Job α) := do
  if self.name ≠ (← getRootPackage).name then
    (← self.fetchOptBuildCache).bindAsync fun _ _ => build
  else
    build

@[deprecated afterBuildCacheAsync (since := "2024-09-27")]
def Package.afterReleaseAsync := @afterBuildCacheAsync

/--
 Perform a build after first checking for an (optional) cloud build
 for the package (e.g., from Reservoir or GitHub).
-/
def Package.afterBuildCacheSync (self : Package) (build : JobM α) : FetchM (Job α) := do
  if self.name ≠ (← getRootPackage).name then
    (← self.fetchOptBuildCache).bindSync fun _ _ => build
  else
    Job.async build

@[deprecated afterBuildCacheSync (since := "2024-09-27")]
def Package.afterReleaseSync := @afterBuildCacheSync

open Package in
/--
A package facet name to build function map that contains builders for
the initial set of Lake package facets (e.g., `extraDep`).
-/
def initPackageFacetConfigs : DNameMap PackageFacetConfig :=
  DNameMap.empty
  |>.insert depsFacet depsFacetConfig
  |>.insert extraDepFacet extraDepFacetConfig
  |>.insert optCacheFacet optCacheFacetConfig
  |>.insert cacheFacet cacheFacetConfig
  |>.insert optBarrelFacet optBarrelFacetConfig
  |>.insert barrelFacet barrelFacetConfig
  |>.insert optReleaseFacet optReleaseFacetConfig
  |>.insert releaseFacet releaseFacetConfig
