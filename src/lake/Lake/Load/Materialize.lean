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

namespace Lake

/-- Update the Git package in `repo` to `rev` if not already at it. -/
def updateGitPkg (repo : GitRepo) (rev? : Option String) : LogIO PUnit := do
  let rev ← repo.findRemoteRevision rev?
  if (← repo.headRevision) == rev then return
  logInfo s!"updating {repo} to revision {rev}"
  repo.checkoutDetach rev

/-- Clone the Git package as `repo`. -/
def cloneGitPkg (repo : GitRepo) (url : String) (rev? : Option String) : LogIO PUnit := do
  logInfo s!"cloning {url} to {repo}"
  repo.clone url
  if let some rev := rev? then
    let hash ← repo.resolveRemoteRevision rev
    repo.checkoutDetach hash

def updateGitRepo (repo : GitRepo) (url : String)
(rev? : Option String) (name : String) : LogIO Unit := do
  if (← repo.dirExists) then
    if (← repo.getRemoteUrl?) = url then
      updateGitPkg repo rev?
    else
      -- TODO: git resolves local file paths so we always hit this case for local repos
      if System.Platform.isWindows then
        -- Deleting git repositories via IO.FS.removeDirAll does not work reliably on windows
        logInfo s!"{name}: URL has changed; you might need to delete {repo.dir} manually"
        updateGitPkg repo rev?
      else
        logInfo s!"{name}: URL has changed; deleting {repo.dir} and cloning again"
        IO.FS.removeDirAll repo.dir
        cloneGitPkg repo url rev?
  else
    cloneGitPkg repo url rev?

structure MaterializeResult where
  relPkgDir : FilePath
  remoteUrl? : Option String
  gitTag? : Option String
  manifestEntry : PackageEntry
  deriving Repr, Inhabited

@[inline] def MaterializeResult.name (self : MaterializeResult) :=
  self.manifestEntry.name

def Source.materialize (src : Source) (name : String)
(wsDir relPkgsDir relParentDir : FilePath) : LogIO MaterializeResult :=
  match src with
  | .path dir =>
    let relPkgDir := relParentDir / dir
    return {
      relPkgDir
      remoteUrl? := none
      gitTag? := none
      manifestEntry := .path name relPkgDir
    }
  | .git url inputRev? subDir? => do
    let relGitDir := relPkgsDir / name
    let repo := GitRepo.mk (wsDir / relGitDir)
    updateGitRepo repo url inputRev? name
    let rev ← repo.headRevision
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    return {
      relPkgDir
      remoteUrl? := Git.filterUrl? url
      gitTag? := ← repo.findTag?
      manifestEntry := .git name url rev inputRev? subDir?
    }

/--
Materializes a package entry, cloning and/or checkout it out as necessary.
-/
def materializePackageEntry (wsDir relPkgsDir : FilePath) (manifestEntry : PackageEntry) : LogIO MaterializeResult :=
  match manifestEntry with
  | .path _name pkgDir =>
    return {
      relPkgDir := pkgDir
      remoteUrl? := none
      gitTag? := none
      manifestEntry
    }
  | .git name url rev _inputRev? subDir? => do
    let relGitDir := relPkgsDir / name
    let gitDir := wsDir / relGitDir
    let repo := GitRepo.mk gitDir
    /-
    Do not update (fetch remote) if already on revision
    Avoids errors when offline e.g. [leanprover/lake#104][104]

    [104]: https://github.com/leanprover/lake/issues/104
    -/
    let updateNecessary ← id do
      if (← repo.dirExists) then
        return (← repo.headRevision?) != rev
      return true
    if updateNecessary then
      updateGitRepo repo url rev name
    let relPkgDir := match subDir? with | .some subDir => relGitDir / subDir | .none => relGitDir
    return {
      relPkgDir
      remoteUrl? := Git.filterUrl? url
      gitTag? := ← repo.findTag?
      manifestEntry
    }
