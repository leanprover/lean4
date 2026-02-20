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
import Lake.Reservoir

open System Lean

/-! # Dependency Materialization
Definitions to "materialize" a package dependency.
That is, clone a local copy of a Git dependency at a specific revision
or resolve a local path dependency.
-/

namespace Lake

/-- Update the Git package in `repo` to `rev` if not already at it. -/
def updateGitPkg
  (name : String) (repo : GitRepo) (rev? : Option String)
: LoggerIO PUnit := do
  let rev ← repo.findRemoteRevision rev?
  if (← repo.getHeadRevision) = rev then
    if (← repo.hasDiff) then
      logWarning s!"{name}: repository '{repo.dir}' has local changes"
  else
    logInfo s!"{name}: checking out revision '{rev}'"
    repo.checkoutDetach rev

/-- Clone the Git package as `repo`. -/
def cloneGitPkg
  (name : String) (repo : GitRepo) (url : String) (rev? : Option String)
: LoggerIO PUnit := do
  logInfo s!"{name}: cloning {url}{(if let some rev := rev? then s!" at revision '{rev}'" else "")}"
  repo.clone url rev?

/--
Update the Git repository from `url` in `repo` to `rev?`.
If `repo` is already from `url`, just checkout the new revision.
Otherwise, delete the local repository and clone a fresh copy from `url`.
-/
def updateGitRepo
  (name : String) (repo : GitRepo) (url : String) (rev? : Option String)
: LoggerIO Unit := do
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
def materializeGitRepo
  (name : String) (repo : GitRepo) (url : String) (rev? : Option String)
: LoggerIO Unit := do
  if (← repo.dirExists) then
    updateGitRepo name repo url rev?
  else
    cloneGitPkg name repo url rev?

public structure MaterializedDep where
  /-- Path to the materialized package relative to the workspace's root directory. -/
  relPkgDir : FilePath
  /--
  URL for the materialized package.
  Used as the endpoint from which to fetch cloud releases for the package.
  -/
  remoteUrl : String
  /-- The manifest entry for the dependency. -/
  manifestEntry : PackageEntry
  deriving Inhabited

namespace MaterializedDep

@[inline] public def name (self : MaterializedDep) :=
  self.manifestEntry.name

@[inline] public def scope (self : MaterializedDep) :=
  self.manifestEntry.scope

/-- Path to the dependency's configuration file (relative to `relPkgDir`). -/
@[inline] public def manifestFile? (self : MaterializedDep) :=
  self.manifestEntry.manifestFile?

/-- Path to the dependency's configuration file (relative to `relPkgDir`). -/
@[inline] public def configFile (self : MaterializedDep) :=
  self.manifestEntry.configFile

end MaterializedDep

inductive InputVer
| none
| git (rev : String)
| ver (ver : VerRange)

def pkgNotIndexed (scope name : String) (ver : InputVer) : String :=
  let (leanVer, tomlVer) :=
    match ver with
    | .none => ("", "")
    | .git rev => (s!" @ {repr rev}", s!"\n    rev = {repr rev}")
    | .ver ver => (s!" @ {repr ver.toString}", s!"\n    version = {repr ver.toString}")
s!"{scope}/{name}: package not found on Reservoir.

  If the package is on GitHub, you can add a Git source. For example:

    require ...
      from git \"https://github.com/{scope}/{name}\"{leanVer}

  or, if using TOML:

    [[require]]
    git = \"https://github.com/{scope}/{name}\"{tomlVer}
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
      return mkDep relPkgDir "" (.path relPkgDir)
    | .git url inputRev? subDir? => do
      let sname := dep.name.toString (escape := false)
      let repoUrl := Git.filterUrl? url |>.getD ""
      materializeGit sname (relPkgsDir / sname) url repoUrl inputRev? subDir?
  else
    if dep.scope.isEmpty then
      error s!"{dep.name}: ill-formed dependency: \
        dependency is missing a source and is missing a scope for Reservoir"
    let ver : InputVer ← id do
      let some ver := dep.version?
        | return .none
      if let some ver := ver.dropPrefix? "git#" then
        return .git ver.toString
      else
        match VerRange.parse ver with
        | .ok ver => return .ver ver
        | .error e =>  error s!"{dep.name}: invalid dependency version range: {e}"
    let depName := dep.name.toString (escape := false)
    let pkg ←
      match (← Reservoir.fetchPkg? lakeEnv dep.scope depName |>.toLogT) with
      | .ok (some pkg) => pure pkg
      | .ok none => error <| pkgNotIndexed dep.scope depName ver
      | .error .. =>
          error s!"{dep.scope}/{depName}: could not materialize package: \
            this may be a transient error or a bug in Lake or Reservoir"
    let relPkgDir := relPkgsDir / pkg.name
    match pkg.gitSrc? with
    | some (.git _ url githubUrl? defaultBranch? subDir?) =>
      let rev? ←
        match ver with
        | .none => defaultBranch?
        | .git rev => some rev
        | .ver ver =>
          match (← Reservoir.fetchPkgVersions lakeEnv dep.scope depName |>.toLogT) with
          | .ok vers =>
              if let some ver := vers.find? (ver.test ·.version) then
                logInfo s!"{dep.scope}/{depName}: using version `{ver.version}` at revision `{ver.revision}`"
                pure ver.revision
              else
                error s!"{dep.scope}/{depName}: version `{ver}` not found on Reservoir"
          | .error .. =>
              error s!"{dep.scope}/{depName}: could not fetch package versions: \
                this may be a transient error or a bug in Lake or Reservoir"
      materializeGit pkg.fullName relPkgDir url (githubUrl?.getD "") rev? subDir?
    | _ => error s!"{pkg.fullName}: Git source not found on Reservoir"
where
  materializeGit name relPkgDir gitUrl remoteUrl inputRev? subDir? : LoggerIO MaterializedDep := do
    let repo := GitRepo.mk (wsDir / relPkgDir)
    let gitUrl := lakeEnv.pkgUrlMap.find? dep.name |>.getD gitUrl
    materializeGitRepo name repo gitUrl inputRev?
    let rev ← repo.getHeadRevision
    let relPkgDir := if let some subDir := subDir? then relPkgDir / subDir else relPkgDir
    return mkDep relPkgDir remoteUrl <| .git gitUrl rev inputRev? subDir?
  @[inline] mkDep relPkgDir remoteUrl src : MaterializedDep := {
    relPkgDir, remoteUrl,
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
    return mkDep relPkgDir ""
  | .git (url := url) (rev := rev) (subDir? := subDir?) .. => do
    let sname := manifestEntry.name.toString (escape := false)
    let relGitDir := relPkgsDir / sname
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
          logWarning s!"{sname}: repository '{repo.dir}' has local changes"
      else
        let url := lakeEnv.pkgUrlMap.find? manifestEntry.name |>.getD url
        updateGitRepo sname repo url rev
    else
      let url := lakeEnv.pkgUrlMap.find? manifestEntry.name |>.getD url
      cloneGitPkg sname repo url rev
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    return mkDep relPkgDir (Git.filterUrl? url |>.getD "")
where
  @[inline] mkDep relPkgDir remoteUrl : MaterializedDep :=
    {relPkgDir, remoteUrl, manifestEntry}
