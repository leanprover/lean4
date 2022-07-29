/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Load.Manifest
import Lake.Config.Dependency

open Std System Lean

namespace Lake

abbrev ManifestM := StateT Manifest <| LogIO

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

/--
Materializes a Git package in `dir`, cloning and/or updating it as necessary.

Attempts to reproduce the `PackageEntry` in the manifest (if one exists) unless
`shouldUpdate` is true. Otherwise, produces the package based on `url` and `rev`
and saves the result to the manifest.
-/
def materializeGitPkg (name : String) (dir : FilePath)
(url : String) (rev? : Option String) (shouldUpdate := true) : ManifestM PUnit := do
  let repo := GitRepo.mk dir
  if let some entry := (← get).find? name then
    if shouldUpdate then
      if (← repo.dirExists) then
        if url = entry.url then
          updateGitPkg repo rev?
        else
          logInfo s!"{name}: URL has changed; deleting {dir} and cloning again"
          IO.FS.removeDirAll dir
          cloneGitPkg repo url rev?
      else
        cloneGitPkg repo url rev?
      let rev ← repo.headRevision
      modify (·.insert {entry with url, rev, inputRev? := rev?})
    else
      if let some rev := rev? then
        if let some inputRev := entry.inputRev? then
          if inputRev ≠ rev then
            logWarning <|
              s!"{name}: revision `{inputRev}` listed in manifest " ++
              s!"does not match `{rev}` listed in the configuration file; " ++
              "you may wish to run `lake update` to update"
      if (← repo.dirExists) then
        if url = entry.url then
          /-
          Do not update (fetch remote) if already on revision
          Avoids errors when offline e.g. [leanprover/lake#104][104]
          [104]: https://github.com/leanprover/lake/issues/104
          -/
          unless (← repo.headRevision) = entry.rev do
            updateGitPkg repo entry.rev
        else
          logWarning <|
            s!"{name}: URL has changed; " ++
            "still using old package, use `lake update` to update"
      else
        cloneGitPkg repo entry.url entry.rev
  else
    if (← repo.dirExists) then
      if shouldUpdate then
        logInfo s!"{name}: no manifest entry; deleting {dir} and cloning again"
        IO.FS.removeDirAll dir
        cloneGitPkg repo url rev?
      else
        logWarning <|
          s!"{name}: no manifest entry; " ++
          "still using old package, use `lake update` to update"
    else
      cloneGitPkg repo url rev?
    let rev ← repo.headRevision
    modify (·.insert {name, url, rev, inputRev? := rev?})

/--
Materializes a `Dependency`, downloading nd/or updating it as necessary.
Local dependencies are materialized relative to `localRoot` and remote
dependencies are stored in `packagesDir`.
-/
def materializeDep (packagesDir localRoot : FilePath) (dep : Dependency)
(shouldUpdate := true) : ManifestM (FilePath × Option String × Option String) :=
  match dep.src with
  | Source.path dir =>
    return (localRoot / dir, none, none)
  | Source.git url rev? subDir? => do
    let name := dep.name.toString (escape := false)
    let gitDir := packagesDir / name
    materializeGitPkg name gitDir url rev? shouldUpdate
    let pkgDir :=
      match subDir? with
      | some subDir => gitDir / subDir
      | none => gitDir
    let tag? ← GitRepo.mk gitDir |>.findTag?
    let url? := Git.filterUrl? url
    return (pkgDir, url?, tag?)
