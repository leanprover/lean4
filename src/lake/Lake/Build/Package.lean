/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.FacetConfig
public import Lake.Build.Job.Monad
public import Lake.Build.Infos
import Lake.Util.Git
import Lake.Util.Url
import Lake.Build.Common
import Lake.Build.Targets
import Lake.Build.Job.Register
import Lake.Reservoir

/-! # Package Facet Builds
Build function definitions for a package's builtin facets.
-/

open System
namespace Lake
open Lean (Name)

/-- Fetch the package's direct dependencies. -/
def Package.recFetchDeps (self : Package) : FetchM (Job (Array Package)) := do
  return Job.pure self.depPkgs

/-- The `PackageFacetConfig` for the builtin `depsFacet`. -/
public def Package.depsFacetConfig : PackageFacetConfig depsFacet :=
  mkFacetJobConfig recFetchDeps (buildable := false)

/-- Compute a topological ordering of the package's transitive dependencies. -/
def Package.recComputeTransDeps (self : Package) : FetchM (Job (Array Package)) := ensureJob do
  (pure ·.toArray) <$> self.depPkgs.foldlM (init := OrdPackageSet.empty) fun deps dep => do
    let depDeps ← (← fetch <| dep.transDeps).await
    return depDeps.foldl (·.insert ·) deps |>.insert dep

/--
Collects the Lean modules of the package's default targets: the modules of each default library,
and the root of each default executable together with its local transitive imports. A default
target that builds no Lean modules, such as a custom target, contributes nothing.
-/
def Package.recCollectDefaultModules (self : Package) : FetchM (Job (Array Module)) := ensureJob do
  let mut mods := #[]
  let mut seen : ModuleSet := ∅
  for target in self.defaultTargets do
    let targetMods ←
      if let some lib := self.findLeanLib? target then
        (← lib.modules.fetch).await
      else if let some exe := self.findLeanExe? target then
        let imports ← (← exe.root.transImports.fetch).await
        pure <| imports.push exe.root
      else
        pure #[]
    for mod in targetMods do
      unless seen.contains mod do
        seen := seen.insert mod
        mods := mods.push mod
  return Job.pure mods

/-- The `PackageFacetConfig` for the builtin `defaultModulesFacet`. -/
public def Package.defaultModulesFacetConfig : PackageFacetConfig defaultModulesFacet :=
  mkFacetJobConfig Package.recCollectDefaultModules (buildable := false)

/-- The `PackageFacetConfig` for the builtin `transDepsFacet`. -/
public def Package.transDepsFacetConfig : PackageFacetConfig transDepsFacet :=
  mkFacetJobConfig recComputeTransDeps (buildable := false)

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub).
-/
def Package.fetchOptBuildCacheCore (self : Package) : FetchM (Job Bool) := do
  if self.preferReleaseBuild then
    self.optGitHubRelease.fetch
  else if self.downloadCacheService?.isSome then
    self.optArtifactCache.fetch
  else
    self.optReservoirBarrel.fetch

/-- The `PackageFacetConfig` for the builtin `optBuildCacheFacet`. -/
public def Package.optBuildCacheFacetConfig : PackageFacetConfig optBuildCacheFacet :=
  mkFacetJobConfig (·.fetchOptBuildCacheCore)

/-- Tries to download the package's build cache (if configured). -/
def Package.maybeFetchBuildCache (self : Package) : FetchM (Job Bool) := do
  let shouldFetch :=
    (← getTryCache)
    && !(← self.buildDir.pathExists) -- do not automatically clobber prebuilt artifacts
    && (
      self.downloadCacheService?.isSome -- artifact caches
      || self.preferReleaseBuild -- GitHub release
      || ( -- Reservoir
        (self.scope == "leanprover" || self.scope == "leanprover-community")
        && !(← getElanToolchain).isEmpty
      )
  )
  if shouldFetch then
    self.optBuildCache.fetch
  else
    return pure true

@[inline]
def Package.optFacetDetails (self : Package) (facet : Name) : JobM String := do
  if (← getIsVerbose) then
    return s!" (see '{self.baseName}:{Name.eraseHead facet}' for details)"
  else
    return " (run with '-v' for details)"

/--
Tries to download and unpack the package's cached build archive
(e.g., from Reservoir or GitHub). Prints a warning on failure.
-/
def Package.maybeFetchBuildCacheWithWarning (self : Package) := do
  let job ← self.maybeFetchBuildCache
  job.mapM fun success => do
    unless success do
      if self.preferReleaseBuild then
        let details ← self.optFacetDetails optGitHubReleaseFacet
        logWarning s!"building from source; failed to fetch GitHub release{details}"
      else if self.downloadCacheService?.isSome then
        let details ← self.optFacetDetails optArtifactCacheFacet
        logVerbose s!"building from source; failed to fetch artifact cache{details}"
      else
        let details ← self.optFacetDetails optReservoirBarrelFacet
        logVerbose s!"building from source; failed to fetch Reservoir build{details}"

/--
Build the `extraDepTargets` for the package.
Also, if the package is a dependency, maybe fetch its build cache.
-/
def Package.recBuildExtraDepTargets (self : Package) : FetchM (Job Unit) :=
  withRegisterJob s!"{self.baseName}:extraDep" do
  let mut job := Job.nil s!"@{self.baseName}:extraDep"
  -- Fetch build cache if this package is a dependency
  unless self.isRoot do
    job := job.add (← self.maybeFetchBuildCacheWithWarning)
  -- Build this package's extra dep targets
  for target in self.extraDepTargets do
    job := job.mix (← self.fetchTargetJob target)
  return job

/-- The `PackageFacetConfig` for the builtin `dynlibFacet`. -/
public def Package.extraDepFacetConfig : PackageFacetConfig extraDepFacet :=
  mkFacetJobConfig Package.recBuildExtraDepTargets

/-- Compute the package's Reservoir barrel URL. -/
def Package.getBarrelUrl (self : Package) : JobM String := do
  if self.scope.isEmpty then
    error "package has no Reservoir scope"
  let repo := GitRepo.mk self.dir
  let some rev ← repo.getHeadRevision?
    | error "failed to resolve HEAD revision"
  let env ← getLakeEnv
  let mut url := Reservoir.pkgApiUrl env self.scope self.reservoirName
  if env.toolchain.isEmpty then
    error "Lean toolchain not known; Reservoir only hosts builds for known toolchains"
  url := s!"{url}/barrel?rev={rev}&toolchain={uriEncode env.toolchain}"
  return url

@[inline]
def mkOptBuildCacheFacetConfig
  {facet : Name} (fetch : Package → JobM PUnit) [FamilyDef FacetOut facet Bool]
: PackageFacetConfig facet := mkFacetJobConfig fun pkg =>
  withRegisterJob s!"{pkg.baseName}:{Name.eraseHead facet}" (optional := true) <| Job.async do
  try
    fetch pkg
    return true
  catch _ =>
    updateAction .fetch
    return false

/-- Tries to download a package's output mappings from its `downloadCacheService`. -/
def Package.fetchArtifactCache (pkg : Package) : JobM PUnit := do
  let some service := pkg.downloadCacheService?
    | error "package has no associated cache service; \
      if you are the maintainer, set `downloadCacheService` on the package"
  let some service := (← getWorkspace).findCacheService? service.toString
    | error s!"package's cache service not found `{service}`; \
      check with the maintainer on how to configure the service"
  let cache ← getLakeCache
  let platform := Internal.cachePlatform pkg .system
  let toolchain := Internal.cacheToolchain pkg (← getWorkspace).cacheToolchain
  let map : CacheMap ← id do
    let repo := GitRepo.mk pkg.dir
    if (← repo.hasDiff) then
      logWarning (Internal.packageHasChanges pkg.prettyName)
    let maxRevs ← getMaxRevs
    let revs ← repo.getHeadRevisions maxRevs
    let map? ← LoggerIO.toLogIO <| revs.findSomeM? fun rev =>
      service.downloadRevisionOutputs? rev cache pkg.cacheScope .none platform toolchain
    let some map := map?
      | error (Internal.noOutputs service .none maxRevs revs)
    return map
  cache.writeMap pkg.cacheScope map service.name? (some .none) (overwrite := false)

/-- The `PackageFacetConfig` for the builtin `optArtifactCacheFacet`. -/
public def Package.optArtifactCacheFacetConfig : PackageFacetConfig optArtifactCacheFacet :=
  mkOptBuildCacheFacetConfig fetchArtifactCache

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
    updateAction .unpack
    untar archiveFile self.buildDir

@[inline]
def mkOptBuildArchiveFacetConfig
  {facet : Name} (archiveFile : Package → FilePath)
  (getUrl : Package → JobM String) (headers : Array String := #[])
  [FamilyDef FacetOut facet Bool]
: PackageFacetConfig facet := mkOptBuildCacheFacetConfig fun pkg => do
    pkg.fetchBuildArchive (← getUrl pkg) (archiveFile pkg) headers

@[inline]
def mkBuildCacheFacetConfig
  {facet : Name} (optFacet : Name) (what : String)
  [FamilyDef FacetOut facet Unit]
  [FamilyDef FacetOut optFacet Bool]
: PackageFacetConfig facet :=
  mkFacetJobConfig fun pkg =>
    withRegisterJob s!"{pkg.baseName}:{Name.eraseHead facet}" do
      (← fetch <| pkg.facetCore optFacet).mapM fun success => do
        unless success do
          error s!"failed to fetch {what}{← pkg.optFacetDetails optFacet}"

/-- The `PackageFacetConfig` for the builtin `buildCacheFacet`. -/
public def Package.buildCacheFacetConfig : PackageFacetConfig buildCacheFacet :=
  mkBuildCacheFacetConfig optBuildCacheFacet "build cache"

/-- The `PackageFacetConfig` for the builtin `artifactCacheFacet`. -/
public def Package.artifactCacheFacetConfig : PackageFacetConfig artifactCacheFacet :=
  mkBuildCacheFacetConfig optArtifactCacheFacet "artifact cache"

/-- The `PackageFacetConfig` for the builtin `optReservoirBarrelFacet`. -/
public def Package.optBarrelFacetConfig : PackageFacetConfig optReservoirBarrelFacet :=
  mkOptBuildArchiveFacetConfig barrelFile getBarrelUrl Reservoir.lakeHeaders

/-- The `PackageFacetConfig` for the builtin `reservoirBarrelFacet`. -/
public def Package.barrelFacetConfig : PackageFacetConfig reservoirBarrelFacet :=
  mkBuildCacheFacetConfig optReservoirBarrelFacet "Reservoir build"

/-- The `PackageFacetConfig` for the builtin `optGitHubReleaseFacet`. -/
public def Package.optGitHubReleaseFacetConfig : PackageFacetConfig optGitHubReleaseFacet :=
  mkOptBuildArchiveFacetConfig buildArchiveFile getReleaseUrl

/-- The `PackageFacetConfig` for the builtin `gitHubReleaseFacet`. -/
public def Package.gitHubReleaseFacetConfig : PackageFacetConfig gitHubReleaseFacet :=
  mkBuildCacheFacetConfig optGitHubReleaseFacet "GitHub release"

/--
Perform a build job after first checking for an (optional) cached build
for the package (e.g., from Reservoir or GitHub).
-/
public def Package.afterBuildCacheAsync (self : Package) (build : JobM (Job α)) : FetchM (Job α) := do
  if self.isRoot then
    build
  else
    (← self.maybeFetchBuildCache).bindM fun _ => do
      setTrace nilTrace -- ensure both branches start with the same trace
      build

/--
 Perform a build after first checking for an (optional) cached build
 for the package (e.g., from Reservoir or GitHub).
-/
public def Package.afterBuildCacheSync (self : Package) (build : JobM α) : FetchM (Job α) := do
  if self.isRoot then
    Job.async build
  else
    (← self.maybeFetchBuildCache).mapM fun _  => do
      setTrace nilTrace -- ensure both branches start with the same trace
      build

/--
A name-configuration map for the initial set of
Lake package facets (e.g., `extraDep`).
-/
public def Package.initFacetConfigs : DNameMap PackageFacetConfig :=
  DNameMap.empty
  |>.insert depsFacet depsFacetConfig
  |>.insert transDepsFacet transDepsFacetConfig
  |>.insert defaultModulesFacet defaultModulesFacetConfig
  |>.insert extraDepFacet extraDepFacetConfig
  |>.insert optBuildCacheFacet optBuildCacheFacetConfig
  |>.insert buildCacheFacet buildCacheFacetConfig
  |>.insert optArtifactCacheFacet optArtifactCacheFacetConfig
  |>.insert artifactCacheFacet artifactCacheFacetConfig
  |>.insert optReservoirBarrelFacet optBarrelFacetConfig
  |>.insert reservoirBarrelFacet barrelFacetConfig
  |>.insert optGitHubReleaseFacet optGitHubReleaseFacetConfig
  |>.insert gitHubReleaseFacet gitHubReleaseFacetConfig

@[inherit_doc Package.initFacetConfigs]
public abbrev initPackageFacetConfigs := Package.initFacetConfigs
