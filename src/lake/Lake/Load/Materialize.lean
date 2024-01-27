/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Load.Manifest
import Lake.Config.Package

open System Lean

/-! # Dependency Materialization
Definitions to "materialize" a package dependency.
That is, clone a local copy of a Git dependency at a specific revision
or resolve a local path dependency.
-/

namespace Lake

/-- Update the Git package in `repo` to `rev` if not already at it. -/
def updateGitPkg (name : String) (repo : GitRepo) (rev? : Option String) : LogIO PUnit := do
  let rev ← repo.findRemoteRevision rev?
  if (← repo.getHeadRevision) = rev then
    if (← repo.hasDiff) then
      logWarning s!"{name}: repository '{repo.dir}' has local changes"
  else
    logInfo s!"{name}: updating repository '{repo.dir}' to revision '{rev}'"
    repo.checkoutDetach rev

/-- Clone the Git package as `repo`. -/
def cloneGitPkg (name : String) (repo : GitRepo)
(url : String) (rev? : Option String) : LogIO PUnit := do
  logInfo s!"{name}: cloning '{url}' to '{repo.dir}'"
  repo.clone url
  if let some rev := rev? then
    let hash ← repo.resolveRemoteRevision rev
    repo.checkoutDetach hash

/--
Update the Git repository from `url` in `repo` to `rev?`.
If `repo` is already from `url`, just checkout the new revision.
Otherwise, delete the local repository and clone a fresh copy from `url`.
-/
def updateGitRepo (name : String) (repo : GitRepo)
(url : String) (rev? : Option String) : LogIO Unit := do
  let sameUrl ← EIO.catchExceptions (h := fun _ => pure false) <| show IO Bool from do
    let some remoteUrl ← repo.getRemoteUrl? | return false
    if remoteUrl = url then return true
    return (← IO.FS.realPath remoteUrl) = (← IO.FS.realPath url)
  if sameUrl then
    updateGitPkg name repo rev?
  else
    if System.Platform.isWindows then
      -- Deleting git repositories via IO.FS.removeDirAll does not work reliably on windows
      logInfo s!"{name}: URL has changed; you might need to delete '{repo.dir}' manually"
      updateGitPkg name repo rev?
    else
      logInfo s!"{name}: URL has changed; deleting '{repo.dir}' and cloning again"
      IO.FS.removeDirAll repo.dir
      cloneGitPkg name repo url rev?

/--
Materialize the Git repository from `url` into `repo` at `rev?`.
Clone it if no local copy exists, otherwise update it.
-/
def materializeGitRepo (name : String) (repo : GitRepo)
(url : String) (rev? : Option String) : LogIO Unit := do
  if (← repo.dirExists) then
    updateGitRepo name repo url rev?
  else
    cloneGitPkg name repo url rev?

structure MaterializedDep where
  /-- Path to the materialized package relative to the workspace's root directory. -/
  relPkgDir : FilePath
  /--
  URL for the materialized package.
  Used as the endpoint from which to fetch cloud releases for the package.
  -/
  remoteUrl? : Option String
  /-- The manifest entry for the dependency. -/
  manifestEntry : PackageEntry
  /-- The configuration-specified package dependency. -/
  depConfig : PackageDepConfig
  deriving Inhabited

@[inline] def MaterializedDep.name (self : MaterializedDep) :=
  self.manifestEntry.name

/-- Path to the dependency's configuration file (relative to `relPkgDir`). -/
@[inline] def MaterializedDep.manifestFile? (self : MaterializedDep) :=
  self.manifestEntry.manifestFile?

/-- Path to the dependency's configuration file (relative to `relPkgDir`). -/
@[inline] def MaterializedDep.configFile (self : MaterializedDep) :=
  self.manifestEntry.configFile

 /-- Lake configuration options for the dependency. -/
@[inline] def MaterializedDep.configOpts (self : MaterializedDep) :=
  self.depConfig.options

local instance : HDiv FilePath (Option FilePath) FilePath where
  hDiv a b? := match b? with | .some b => a / b | .none => a

inductive RegistrySrc
| git (url : String) (defaultBranch? : Option String) (data : JsonObject)
| github (id fullName repoUrl gitUrl: String) (defaultBranch? : Option String)
| other (data : JsonObject)
namespace RegistrySrc

@[inline] def git? (src : RegistrySrc) : Option (String × Option String) :=
  match src with
  | .git url branch? .. => some (url, branch?)
  | .github (gitUrl := url) (defaultBranch? := branch?) .. => some (url, branch?)
  | _ => none

@[inline] def gitUrl? (src : RegistrySrc) : Option String :=
  match src with
  | .git url .. => some url
  | .github (gitUrl := url) .. => some url
  | _ => none

@[inline] def githubUrl? (src : RegistrySrc) : Option String :=
  match src with
  | .github (repoUrl := url) .. => some url
  | _ => none

protected def fromJson? (val : Json) : Except String RegistrySrc :=
  try
    let obj ← JsonObject.fromJson? val
    let host ← obj.get "host"
    match host with
    | "github" =>
      let id ← obj.get "id"
      let fullName ← obj.get "fullName"
      let repoUrl ← obj.get "repoUrl"
      let gitUrl ← obj.get "gitUrl"
      let defaultBranch? ← obj.get? "defaultBranch"
      return .github id fullName repoUrl gitUrl defaultBranch?
    | _ =>
      if let some url ← obj.get? "gitUrl" then
        let defaultBranch? ← obj.get? "defaultBranch"
        let obj := obj.erase "gitUrl" |>.erase "defaultBranch"
        return .git url defaultBranch? obj
      else
        return .other obj
  catch e =>
    throw s!"source: {e}"

instance : FromJson RegistrySrc := ⟨RegistrySrc.fromJson?⟩

end RegistrySrc

structure RegistryPkg where
  name : String
  fullName : String
  sources : Array RegistrySrc

namespace RegistryPkg

def git? (pkg : RegistryPkg) : Option (String × Option String) :=
  pkg.sources.findSome? (·.git?)

def gitUrl? (pkg : RegistryPkg) : Option String :=
  pkg.sources.findSome? (·.gitUrl?)

def githubUrl? (pkg : RegistryPkg) : Option String :=
  pkg.sources.findSome? (·.githubUrl?)

protected def fromJson? (val : Json) : Except String RegistryPkg := do
  let obj ← JsonObject.fromJson? val
  let name ← obj.get "name"
  let fullName ← obj.get "fullName"
  let sources ← (← obj.getD "sources" #[]).mapM fromJson?
  return {name, fullName, sources}

instance : FromJson RegistryPkg := ⟨RegistryPkg.fromJson?⟩

end RegistryPkg

def getUrl (url : String) (headers : Array String := #[]) : LogIO String := do
  let args := #["-s", "-f", "-L"]
  let args := headers.foldl (init := args) (· ++ #["-H", ·])
  captureProc {cmd := "curl", args := args.push url}

def fetchRegistryPkg (env : Lake.Env) (pkg : String) : LogIO RegistryPkg := do
  let url := s!"{env.reservoirUrl}/v0/packages/{pkg}"
  let out ← getUrl url #["X-Reservoir-Registry-Api-Version:0.1.0"]
    <|> error s!"{pkg}: failed to lookup package on Reservoir"
  match Json.parse out >>= fromJson? with
  | .ok json =>
    match fromJson? json with
    | .ok pkg => pure pkg
    | .error e => error s!"{pkg}: Reservoir returned unsupported JSON: {e}"
  | .error _ => error s!"{pkg}: failed to lookup package on Reservoir (invalid JSON)"

@[inline] def extractGit (pkg : RegistryPkg) : LogIO (String × Option String)  := do
  let some (url, defaultBranch?) := pkg.git?
    | error "{pkg.fullName}: no Git source found in Lake's default registry (Reservoir)"
  return (url, defaultBranch?)

@[inline] def extractGitUrl (pkg : RegistryPkg) : LogIO String := do
  let some url := pkg.gitUrl?
    | error "{pkg.fullName}: no Git source URL found in Lake's default registry (Reservoir)"
  return url

/--
Materializes a configuration package dependency.
For Git dependencies, updates it to the latest input revision.
-/
def PackageDepConfig.materialize (dep : PackageDepConfig) (inherited : Bool)
(wsDir relPkgsDir relParentDir : FilePath) (env : Lake.Env)
: LogIO MaterializedDep := do
  if let some src := dep.source? then
    match src with
    | .path dir =>
      let relPkgDir := relParentDir / dir
      return {
        relPkgDir
        remoteUrl? := none
        manifestEntry := mkEntry <| .path relPkgDir
        depConfig := dep
      }
    | .git url inputRev? subDir? =>
      let relGitDir := relPkgsDir / dep.fullName
      let rev ← materializeGit dep.fullName relGitDir url inputRev?
      return {
        relPkgDir := relGitDir / subDir?
        remoteUrl? := Git.filterUrl? url
        manifestEntry := mkEntry <| .git url rev inputRev? subDir?
        depConfig := dep
      }
    | .github owner repo inputRev? subDir? =>
        let url := s!"{env.githubUrl}/{owner}/{repo}"
        let relGitDir := relPkgsDir / dep.name
        let rev ← materializeGit dep.fullName relGitDir url inputRev?
        return {
          relPkgDir := relGitDir / subDir?
          remoteUrl? := url
          manifestEntry := mkEntry <| .github owner repo rev inputRev? subDir?
          depConfig := dep
        }
  else
    let pkg ← fetchRegistryPkg env dep.fullName
    let (url, defaultBranch?) ← extractGit pkg
    let relPkgDir := relPkgsDir / pkg.name
    let rev? := dep.version? <|> defaultBranch?
    let rev ← materializeGit dep.fullName relPkgDir url rev?
    return {
      relPkgDir
      remoteUrl? := pkg.githubUrl?
      manifestEntry := mkEntry <| .registry rev dep.version?
      depConfig := dep
    }
where
  mkEntry source : PackageEntry := {
    name := dep.name, fullName := dep.fullName,
    conditional := dep.conditional, inherited, source
  }
  materializeGit name relGitDir url inputRev? := do
    let repo := GitRepo.mk (wsDir / relGitDir)
    let materializeUrl := env.pkgUrlMap.find? name |>.getD url
    materializeGitRepo name repo materializeUrl inputRev?
    repo.getHeadRevision

/--
Materializes a manifest package entry, cloning and/or checking it out as necessary.
-/
def PackageEntry.materialize (manifestEntry : PackageEntry)
(depConfig : PackageDepConfig) (wsDir relPkgsDir : FilePath) (env : Lake.Env)
: LogIO MaterializedDep := do
  match manifestEntry.source with
  | .path (dir := relPkgDir) .. =>
    return {relPkgDir, manifestEntry, depConfig, remoteUrl? := none}
  | .git (url := url) (rev := rev) (subDir? := subDir?) .. =>
    let relPkgDir ← materializeGit url rev subDir?
    let remoteUrl? := Git.filterUrl? url
    return {relPkgDir, manifestEntry, depConfig, remoteUrl?}
  | .github (owner := owner) (repo := repo) (rev := rev) (subDir? := subDir?) .. =>
    let url := s!"{env.githubUrl}/{owner}/{repo}"
    let relPkgDir ← materializeGit url rev subDir?
    return {relPkgDir, manifestEntry, depConfig, remoteUrl? := url}
  | .registry (rev := rev) .. =>
    let pkg ← fetchRegistryPkg env depConfig.fullName
    let url ← extractGitUrl pkg
    let relPkgDir ← materializeGit url rev none
    return {relPkgDir, manifestEntry, depConfig, remoteUrl? := pkg.githubUrl?}
where
  materializeGit url rev subDir? := do
    let name := manifestEntry.name
    let relGitDir := relPkgsDir / name.toString
    let gitDir := wsDir / relGitDir
    let repo := GitRepo.mk gitDir
    /-
    Do not update (fetch remote) if already on revision
    Avoids errors when offline, e.g., [leanprover/lake#104][104].

    [104]: https://github.com/leanprover/lake/issues/104
    -/
    if (← repo.dirExists) then
      if (← repo.getHeadRevision?) = rev then
        if (← repo.hasDiff) then
          logWarning s!"{name}: repository '{repo.dir}' has local changes"
      else
        let url := env.pkgUrlMap.find? name |>.getD url
        updateGitRepo name repo url rev
    else
      let url := env.pkgUrlMap.find? name |>.getD url
      cloneGitPkg name repo url rev
    return relGitDir / subDir?
