/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Load.Manifest
import Lake.Config.Dependency
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
def cloneGitPkg (name : Name) (repo : GitRepo)
(url : String) (rev? : Option String) : LogIO PUnit := do
  logInfo s!"{name}: cloning {url} to '{repo.dir}'"
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
  /-- The configuration-specified dependency. -/
  configDep : Dependency
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
  self.configDep.opts

/--
Materializes a configuration dependency.
For Git dependencies, updates it to the latest input revision.
-/
def Dependency.materialize (dep : Dependency) (inherited : Bool)
(wsDir relPkgsDir relParentDir : FilePath) (pkgUrlMap : NameMap String)
: LogIO MaterializedDep :=
  match dep.src with
  | .path dir =>
    let relPkgDir := relParentDir / dir
    return {
      relPkgDir
      remoteUrl? := none
      manifestEntry := .path dep.name inherited defaultConfigFile none relPkgDir
      configDep := dep
    }
  | .git url inputRev? subDir? => do
    let sname := dep.name.toString (escape := false)
    let relGitDir := relPkgsDir / sname
    let repo := GitRepo.mk (wsDir / relGitDir)
    let materializeUrl := pkgUrlMap.find? dep.name |>.getD url
    materializeGitRepo sname repo materializeUrl inputRev?
    let rev ← repo.getHeadRevision
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    return {
      relPkgDir
      remoteUrl? := Git.filterUrl? url
      manifestEntry := .git dep.name inherited defaultConfigFile none url rev inputRev? subDir?
      configDep := dep
    }

/--
Materializes a manifest package entry, cloning and/or checking it out as necessary.
-/
def PackageEntry.materialize (manifestEntry : PackageEntry)
(configDep : Dependency) (wsDir relPkgsDir : FilePath) (pkgUrlMap : NameMap String)
: LogIO MaterializedDep :=
  match manifestEntry with
  | .path (dir := relPkgDir) .. =>
    return {
      relPkgDir
      remoteUrl? := none
      manifestEntry
      configDep
    }
  | .git name (url := url) (rev := rev) (subDir? := subDir?) .. => do
    let sname := name.toString (escape := false)
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
        let url := pkgUrlMap.find? name |>.getD url
        updateGitRepo sname repo url rev
    else
      let url := pkgUrlMap.find? name |>.getD url
      cloneGitPkg sname repo url rev
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    return {
      relPkgDir
      remoteUrl? := Git.filterUrl? url
      manifestEntry
      configDep
    }
