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
open Lean (Name)

/-- Compute a topological ordering of the package's transitive dependencies. -/
def Package.recComputeDeps (self : Package) : FetchM (Array Package) := do
  (·.toArray) <$> self.depConfigs.foldlM (init := OrdPackageSet.empty) fun deps cfg => do
    let some dep ← findPackage? cfg.name
      | error s!"{self.name}: package not found for dependency '{cfg.name}' \
        (this is likely a bug in Lake)"
    return (← fetch <| dep.facet `deps).foldl (·.insert ·) deps |>.insert dep

/-- The `PackageFacetConfig` for the builtin `depsFacet`. -/
def Package.depsFacetConfig : PackageFacetConfig depsFacet :=
  mkFacetConfig Package.recComputeDeps

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub).
-/
private def Package.fetchOptBuildCacheCore (self : Package) : FetchM (BuildJob Bool) := do
  if self.preferReleaseBuild then
    self.optGitHubRelease.fetch
  else
    self.optReservoirBarrel.fetch

/-- The `PackageFacetConfig` for the builtin `optBuildCacheFacet`. -/
def Package.optBuildCacheFacetConfig : PackageFacetConfig optBuildCacheFacet :=
  mkFacetJobConfig (·.fetchOptBuildCacheCore)

/-- Tries to download the package's build cache (if configured). -/
def Package.maybeFetchBuildCache (self : Package) : FetchM (BuildJob Bool) := do
  let shouldFetch :=
    (← getTryCache) &&
    (self.preferReleaseBuild || -- GitHub release
      ((self.scope == "leanprover" || self.scope == "leanprover-community")
        && !(← getElanToolchain).isEmpty
        && !(← self.buildDir.pathExists))) -- Reservoir
  if shouldFetch then
    self.optBuildCache.fetch
  else
    return pure true

@[inline]
private def Package.optFacetDetails (self : Package) (facet : Name) : JobM String := do
  if (← getIsVerbose) then
    return s!" (see '{self.name}:{facet}' for details)"
  else
    return " (run with '-v' for details)"

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub). Prints a warning on failure.
-/
def Package.maybeFetchBuildCacheWithWarning (self : Package) := do
  let job ← self.maybeFetchBuildCache
  job.bindSync fun success t => do
    unless success do
      if self.preferReleaseBuild then
        let details ← self.optFacetDetails optGitHubReleaseFacet
        logWarning s!"building from source; failed to fetch GitHub release{details}"
      else
        let details ← self.optFacetDetails optReservoirBarrelFacet
        logVerbose s!"building from source; failed to fetch Reservoir build{details}"
    return ((), t)

@[deprecated maybeFetchBuildCacheWithWarning (since := "2024-09-27")]
def Package.fetchOptRelease := @maybeFetchBuildCacheWithWarning

/--
Build the `extraDepTargets` for the package.
Also, if the package is a dependency, maybe fetch its build cache.
-/
def Package.recBuildExtraDepTargets (self : Package) : FetchM (BuildJob Unit) :=
  withRegisterJob s!"{self.name}:extraDep" do
  let mut job := BuildJob.nil
  -- Fetch build cache if this package is a dependency
  if self.name ≠ (← getWorkspace).root.name then
    job := job.add <| ← self.maybeFetchBuildCacheWithWarning
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
  let env ← getLakeEnv
  let mut url := Reservoir.pkgApiUrl env self.scope pkgName
  if env.toolchain.isEmpty then
    error "Lean toolchain not known; Reservoir only hosts builds for known toolchains"
  url := s!"{url}/barrel?rev={rev}&toolchain={uriEncode env.toolchain}"
  return url

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
def Package.fetchBuildArchive
  (self : Package) (url : String) (archiveFile : FilePath)
  (headers : Array String := #[])
: JobM PUnit := do
  let depTrace := Hash.ofString url
  let traceFile := archiveFile.addExtension "trace"
  let upToDate ← buildUnlessUpToDate? (action := .fetch) archiveFile depTrace traceFile do
    download url archiveFile headers
  unless upToDate && (← self.buildDir.pathExists) do
    updateAction .fetch
    untar archiveFile self.buildDir

@[inline]
private def Package.mkOptBuildArchiveFacetConfig
  {facet : Name} (archiveFile : Package → FilePath)
  (getUrl : Package → JobM String) (headers : Array String := #[])
  [FamilyDef PackageData facet (BuildJob Bool)]
: PackageFacetConfig facet := mkFacetJobConfig fun pkg =>
  withRegisterJob s!"{pkg.name}:{facet}" (optional := true) <| Job.async do
  try
    let url ← getUrl pkg
    pkg.fetchBuildArchive url (archiveFile pkg) headers
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
          error s!"failed to fetch {what}{← pkg.optFacetDetails optFacet}"
        return ((), t)

/-- The `PackageFacetConfig` for the builtin `buildCacheFacet`. -/
def Package.buildCacheFacetConfig : PackageFacetConfig buildCacheFacet :=
  mkBuildArchiveFacetConfig optBuildCacheFacet "build cache"

/-- The `PackageFacetConfig` for the builtin `optReservoirBarrelFacet`. -/
def Package.optBarrelFacetConfig : PackageFacetConfig optReservoirBarrelFacet :=
  mkOptBuildArchiveFacetConfig barrelFile getBarrelUrl Reservoir.lakeHeaders

/-- The `PackageFacetConfig` for the builtin `reservoirBarrelFacet`. -/
def Package.barrelFacetConfig : PackageFacetConfig reservoirBarrelFacet :=
  mkBuildArchiveFacetConfig optReservoirBarrelFacet "Reservoir build"

/-- The `PackageFacetConfig` for the builtin `optGitHubReleaseFacet`. -/
def Package.optGitHubReleaseFacetConfig : PackageFacetConfig optGitHubReleaseFacet :=
  mkOptBuildArchiveFacetConfig buildArchiveFile getReleaseUrl

@[deprecated (since := "2024-09-27")]
abbrev Package.optReleaseFacetConfig := optGitHubReleaseFacetConfig

/-- The `PackageFacetConfig` for the builtin `gitHubReleaseFacet`. -/
def Package.gitHubReleaseFacetConfig : PackageFacetConfig gitHubReleaseFacet :=
  mkBuildArchiveFacetConfig optGitHubReleaseFacet "GitHub release"

@[deprecated (since := "2024-09-27")]
abbrev Package.releaseFacetConfig := gitHubReleaseFacetConfig

/--
Perform a build job after first checking for an (optional) cached build
for the package (e.g., from Reservoir or GitHub).
-/
def Package.afterBuildCacheAsync (self : Package) (build : SpawnM (Job α)) : FetchM (Job α) := do
  if self.name ≠ (← getRootPackage).name then
    (← self.maybeFetchBuildCache).bindAsync fun _ _ => build
  else
    build

@[deprecated afterBuildCacheAsync (since := "2024-09-27")]
def Package.afterReleaseAsync := @afterBuildCacheAsync

/--
 Perform a build after first checking for an (optional) cached build
 for the package (e.g., from Reservoir or GitHub).
-/
def Package.afterBuildCacheSync (self : Package) (build : JobM α) : FetchM (Job α) := do
  if self.name ≠ (← getRootPackage).name then
    (← self.maybeFetchBuildCache).bindSync fun _ _ => build
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
  |>.insert optBuildCacheFacet optBuildCacheFacetConfig
  |>.insert buildCacheFacet buildCacheFacetConfig
  |>.insert optReservoirBarrelFacet optBarrelFacetConfig
  |>.insert reservoirBarrelFacet barrelFacetConfig
  |>.insert optGitHubReleaseFacet optGitHubReleaseFacetConfig
  |>.insert gitHubReleaseFacet gitHubReleaseFacetConfig
