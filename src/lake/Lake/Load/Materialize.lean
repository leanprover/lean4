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
def updateGitPkg (repo : GitRepo) (rev? : Option String) (name : String) : LogIO PUnit := do
  let rev ← repo.findRemoteRevision rev?
  if (← repo.getHeadRevision) = rev then
    if (← repo.hasDiff) then
      logWarning s!"{name}: repository '{repo.dir}' has local changes"
  else
    logInfo s!"{name}: updating repository '{repo.dir}' to revision '{rev}'"
    repo.checkoutDetach rev

/-- Clone the Git package as `repo`. -/
def cloneGitPkg (repo : GitRepo) (url : String) (rev? : Option String) : LogIO PUnit := do
  logInfo s!"cloning {url} to {repo}"
  repo.clone url
  if let some rev := rev? then
    let hash ← repo.resolveRemoteRevision rev
    repo.checkoutDetach hash

/--
Update the Git repository from `url` in `repo` to `rev?`.
If `repo` is already from `url`, just checkout the new revision.
Otherwise, delete the local repository and clone a fresh copy from `url`.
-/
def updateGitRepo (repo : GitRepo) (url : String)
(rev? : Option String) (name : String) : LogIO Unit := do
  let sameUrl ← EIO.catchExceptions (h := fun _ => pure false) <| show IO Bool from do
    let some remoteUrl ← repo.getRemoteUrl? | return false
    if remoteUrl = url then return true
    return (← IO.FS.realPath remoteUrl) = (← IO.FS.realPath url)
  if sameUrl then
    updateGitPkg repo rev? name
  else
    if System.Platform.isWindows then
      -- Deleting git repositories via IO.FS.removeDirAll does not work reliably on windows
      logInfo s!"{name}: URL has changed; you might need to delete '{repo.dir}' manually"
      updateGitPkg repo rev? name
    else
      logInfo s!"{name}: URL has changed; deleting '{repo.dir}' and cloning again"
      IO.FS.removeDirAll repo.dir
      cloneGitPkg repo url rev?

/--
Materialize the Git repository from `url` into `repo` at `rev?`.
Clone it if no local copy exists, otherwise update it.
-/
def materializeGitRepo (repo : GitRepo) (url : String)
(rev? : Option String) (name : String) : LogIO Unit := do
  if (← repo.dirExists) then
    updateGitRepo repo url rev? name
  else
    cloneGitPkg repo url rev?

structure MaterializedDep where
  /-- Path to the materialized package relative to the workspace's root directory. -/
  relPkgDir : FilePath
  remoteUrl? : Option String
  manifestEntry : PackageEntry
  deriving Inhabited

@[inline] def MaterializedDep.name (self : MaterializedDep) :=
  self.manifestEntry.name

@[inline] def MaterializedDep.opts (self : MaterializedDep) :=
  self.manifestEntry.opts

/--
Materializes a configuration dependency.
For Git dependencies, updates it to the latest input revision.
-/
def Dependency.materialize (dep : Dependency) (inherited : Bool)
(wsDir relPkgsDir relParentDir : FilePath) : LogIO MaterializedDep :=
  match dep.src with
  | .path dir =>
    let relPkgDir := relParentDir / dir
    return {
      relPkgDir
      remoteUrl? := none
      manifestEntry := .path dep.name dep.opts inherited relPkgDir
    }
  | .git url inputRev? subDir? => do
    let name := dep.name.toString (escape := false)
    let relGitDir := relPkgsDir / name
    let repo := GitRepo.mk (wsDir / relGitDir)
    materializeGitRepo repo url inputRev? name
    let rev ← repo.getHeadRevision
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    return {
      relPkgDir
      remoteUrl? := Git.filterUrl? url
      manifestEntry := .git dep.name dep.opts inherited url rev inputRev? subDir?
    }

/--
Materializes a manifest package entry, cloning and/or checking it out as necessary. -/
def PackageEntry.materialize (wsDir relPkgsDir : FilePath) (manifestEntry : PackageEntry) : LogIO MaterializedDep :=
  match manifestEntry with
  | .path _name _opts _inherited relPkgDir =>
    return {
      relPkgDir
      remoteUrl? := none
      manifestEntry
    }
  | .git name _opts _inherited url rev _inputRev? subDir? => do
    let name := name.toString (escape := false)
    let relGitDir := relPkgsDir / name
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
        updateGitRepo repo url rev name
    else
      cloneGitPkg repo url rev
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    return {
      relPkgDir
      remoteUrl? := Git.filterUrl? url
      manifestEntry
    }
