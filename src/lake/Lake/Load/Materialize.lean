/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
module

prelude
public import Lake.Config.Env
public import Lake.Load.Manifest
public import Lake.Config.Package
import Lake.Util.Git
import Lake.Util.IO
import Lake.Reservoir

set_option doc.verso true

open System Lean

/-! # Dependency Materialization
Definitions to "materialize" a package dependency.
That is, clone a local copy of a Git dependency at a specific revision
or resolve a local path dependency.
-/

namespace Lake

/--
Materialize the Git repository from {lean}`url` into {lean}`repo` at {lean}`rev?`.

If no revision is specified (i.e., {lean}`rev? = none`), the latest {lit}`master` is used.

If the repository is already at {lean}`rev?`, return early with no fetch.
Otherwise, fetch the revision {lean}`rev?` from the remote {lean}`url` and check it out.
If no local repository exists, initialize a new one.
-/
def materializeGitRepo
  (name : String) (repo : GitRepo) (url : String) (rev? : Option GitRev)
: LoggerIO Unit := do
  let rev := rev?.getD Git.upstreamBranch
  let remote := Git.defaultRemote
  let url ← resolveUrl url
  -- # Setup repository
  if (← repo.gitExists) then
    -- The URL may be updated even without a `lake update`.
    -- This ensures a package's `remoteUrl?` reflects Git's by default.
    if let some oldUrl ← repo.getRemoteUrl? remote then
      unless oldUrl = url do
        logInfo s!"{name}: remote URL changed\
          \n  old: {oldUrl}\
          \n  new: {url}"
        repo.setRemoteUrl remote url
    else
      repo.addRemote remote url
    -- Skip fetch if already on revision. Avoids errors when offline.
    -- https://github.com/leanprover/lake/issues/104
    if (← repo.getHeadRevision?) = some rev then
      checkDiff
      return
    if rev.isFullSha1 then
      -- If missing, `findCommit?` will fetch to try and find it (on a partial clone).
      -- This could be avoided with `--no-lazy-fetch`, but that requires Git 2.45+.
      -- Fetch will happen anyway next, so the higher minimum is not worth it.
      if (← repo.findCommit? rev).isSome then
        -- Skip revision fetch if the exact commit is already available.
        -- May still fetch objects due to the partial clone.
        checkout rev
        return
  else
    logInfo s!"{name}: materializing new dependency"
    IO.FS.createDirAll repo.dir
    repo.quietInit
    repo.addRemote remote url
  -- # New revision
  logInfo s!"{name}: fetching revision '{rev}' from {url}"
  let some rev ← repo.fetchRevision? remote rev
    | error s!"{name}: failed to fetch the package revision\
      \n  {rev}\
      \nfrom the Git repository at\
      \n  {url}"
  if (← repo.getHeadRevision?) = some rev then -- e.g., new tag = old rev
    checkDiff
    return
  checkout rev
  -- Cleanup unreachable references and objects to prevent excessive repository growth
  repo.pruneRemote remote
  repo.gcAuto
where
  @[inline] resolveUrl url := do
    if (← FilePath.pathExists url) then
      let some path ← resolvePath? url
        | error s!"{name}: failed to resolve path:\n  {url}"
      return path.toString
    else
      return url
  @[inline] checkout rev := do
    logInfo s!"{name}: checking out revision '{rev}'"
    repo.checkoutDetach rev
    -- Remove untracked files from tracked folders in the package.
    -- This helps ensure reproducible behavior by removing leftovers.
    -- For example, Lake will trust leftover `.hash` files unconditionally,
    -- so stale ones from the previous revision cause incorrect trace computations.
    repo.clean
    checkDiff
  @[inline] checkDiff := do
    if (← repo.hasDiff) then
      logWarning s!"{name}: repository has local changes:\n  {repo.dir}"

public structure MaterializedDep where
  /-- Absolute path to the materialized package. -/
  pkgDir : FilePath
  /-- Path to the materialized package relative to the workspace's root directory. -/
  relPkgDir : FilePath
  /--
  URL for the materialized package.
  Used as the endpoint from which to fetch cloud releases for the package.
  -/
  remoteUrl : String
  /-- The manifest for the dependency or the error produced when trying to load it. -/
  manifest? : Except IO.Error Manifest
  /-- The manifest entry for the dependency. -/
  manifestEntry : PackageEntry
  deriving Inhabited

namespace MaterializedDep

@[inline] public def name (self : MaterializedDep) : Name :=
  self.manifestEntry.name

@[inline] public def prettyName (self : MaterializedDep) : String :=
  self.manifestEntry.name.toString (escape := false)

@[inline] public def scope (self : MaterializedDep) : String :=
  self.manifestEntry.scope

/-- Path to the dependency's manfiest file (relative to {lean}`relPkgDir`). -/
@[inline] public def relManifestFile? (self : MaterializedDep) : Option FilePath :=
  self.manifestEntry.manifestFile?

/-- Path to the dependency's manfiest file (relative to {lean}`relPkgDir`). -/
@[inline] public def relManifestFile (self : MaterializedDep) : FilePath :=
  self.relManifestFile?.getD defaultManifestFile

/-- Absolute path to the dependency's manfiest file. -/
@[inline] public def manifestFile (self : MaterializedDep) : FilePath :=
  self.pkgDir / self.relManifestFile

/-- Path to the dependency's configuration file (relative to {lean}`relPkgDir`). -/
@[inline] public def relConfigFile (self : MaterializedDep) : FilePath :=
  self.manifestEntry.configFile

/-- Absolute path to the dependency's configuration file. -/
@[inline] public def configFile (self : MaterializedDep) : FilePath :=
  self.pkgDir / self.relConfigFile

public def fixedToolchain (self : MaterializedDep) : Bool :=
  match self.manifest? with
  | .ok manifest => manifest.fixedToolchain
  | _ => false

end MaterializedDep

def pkgNotIndexed (dep : Dependency) : String :=
  let (leanVer, tomlVer) :=
    match dep.version with
    | .none => ("", "")
    | .git rev => (s!" @ {repr rev}", s!"\n    rev = {repr rev}")
    | .ver ver => (s!" @ {repr ver.toString}", s!"\n    version = {repr ver.toString}")
s!"{dep.fullName}: package not found on Reservoir.

  If the package is on GitHub, you can add a Git source. For example:

    require ...
      from git \"https://github.com/{dep.scope}/{dep.reservoirName}\"{leanVer}

  or, if using TOML:

    [[require]]
    git = \"https://github.com/{dep.scope}/{dep.reservoirName}\"{tomlVer}
    ...
"

/--
Materializes a configuration dependency.
For Git dependencies, updates it to the latest input revision.
-/
public def Dependency.materialize
  (dep : Dependency) (inherited : Bool)
  (lakeEnv : Env) (wsDir relPkgsDir relParentDir : FilePath)
: LoggerIO MaterializedDep := do
  if let some src := dep.src? then
    match src with
    | .path dir =>
      let relPkgDir := relParentDir / dir
      mkDep dep.prettyName relPkgDir "" (.path relPkgDir)
    | .git url inputRev? subDir? => do
      let repoUrl := Git.filterUrl? url |>.getD ""
      materializeGit dep.prettyName (relPkgsDir / dep.dirName) url repoUrl inputRev? subDir?
  else
    if dep.scope.isEmpty then
      error s!"{dep.prettyName}: ill-formed dependency: \
        dependency is missing a source and is missing a scope for Reservoir"
    let pkg ← id do
      match (← Reservoir.fetchPkg? lakeEnv dep.scope dep.reservoirName |>.toLogT) with
      | .ok (some pkg) => return pkg
      | .ok none => error <| pkgNotIndexed dep
      | .error .. => error s!"{dep.fullName}: could not materialize package: \
        this may be a transient error or a bug in Lake or Reservoir"
    let relPkgDir := relPkgsDir / pkg.name
    match pkg.gitSrc? with
    | some (.git _ url githubUrl? defaultBranch? subDir?) =>
      let rev? ← id do
        match dep.version with
        | .none => defaultBranch?
        | .git rev => some rev
        | .ver ver =>
          match (← Reservoir.fetchPkgVersions lakeEnv dep.scope dep.reservoirName |>.toLogT) with
          | .ok vers =>
            if let some ver := vers.find? (ver.test ·.version) then
              logInfo s!"{dep.fullName}: using version `{ver.version}` at revision `{ver.revision}`"
              return ver.revision
            else
              error s!"{dep.fullName}: version `{ver}` not found on Reservoir"
          | .error .. => error s!"{dep.fullName}: could not fetch package versions: \
            this may be a transient error or a bug in Lake or Reservoir"
      materializeGit pkg.fullName relPkgDir url (githubUrl?.getD "") rev? subDir?
    | _ => error s!"{pkg.fullName}: Git source not found on Reservoir"
where
  materializeGit name relPkgDir gitUrl remoteUrl inputRev? subDir? : LoggerIO MaterializedDep := do
    let gitDir := wsDir / relPkgDir
    let repo := GitRepo.mk gitDir
    let gitUrl := lakeEnv.pkgUrlMap.find? dep.name |>.getD gitUrl
    materializeGitRepo name repo gitUrl inputRev?
    let rev ← repo.getHeadRevision
    let relPkgDir := if let some subDir := subDir? then relPkgDir / subDir else relPkgDir
    mkDep name relPkgDir remoteUrl <| .git gitUrl rev inputRev? subDir?
  @[inline] mkDep name relPkgDir remoteUrl src : LoggerIO MaterializedDep := do
    let pkgDir := wsDir / relPkgDir
    let some pkgDir ← resolvePath? pkgDir
      | error s!"{name}: package directory not found: {pkgDir}"
    return {
      pkgDir, relPkgDir, remoteUrl,
      manifest? :=  ← Manifest.load (pkgDir / defaultManifestFile) |>.toBaseIO
      manifestEntry := {name := dep.name, scope := dep.scope, inherited, src}
    }

/--
Materializes a manifest package entry, cloning and/or checking it out as necessary.
-/
public def PackageEntry.materialize
  (manifestEntry : PackageEntry)
  (lakeEnv : Env) (wsDir relPkgsDir : FilePath)
: LoggerIO MaterializedDep :=
  match manifestEntry.src with
  | .path (dir := relPkgDir) .. =>
    mkDep relPkgDir ""
  | .git (url := url) (rev := rev) (subDir? := subDir?) .. => do
    let relGitDir := relPkgsDir / manifestEntry.dirName
    let repo := GitRepo.mk (wsDir / relGitDir)
    let url := lakeEnv.pkgUrlMap.getD manifestEntry.name url
    materializeGitRepo manifestEntry.prettyName repo url rev
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    mkDep relPkgDir (Git.filterUrl? url |>.getD "")
where
  @[inline] mkDep relPkgDir remoteUrl : LoggerIO MaterializedDep := do
    let pkgDir := wsDir / relPkgDir
    let some pkgDir ← resolvePath? pkgDir
      | error s!"{manifestEntry.prettyName}: package directory not found: {pkgDir}"
    let manifest? ← id do
      if let some manifestFile := manifestEntry.manifestFile? then
        Manifest.load (pkgDir / manifestFile) |>.toBaseIO
      else
        return .error (.noFileOrDirectory "" 0 "")
    return {pkgDir, relPkgDir, remoteUrl, manifest?, manifestEntry}
