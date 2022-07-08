/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Util.EStateT
import Lake.Util.StoreInsts
import Lake.Config.Load
import Lake.Config.Manifest
import Lake.Config.Workspace
import Lake.Build.Topological

open Std System

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
    let hash ← repo.parseRemoteRevision rev
    repo.checkoutDetach hash

abbrev ResolveM := StateT (NameMap PackageEntry) <| LogIO

/--
Materializes a Git package in `dir`, cloning and/or updating it as necessary.

Attempts to reproduce the `PackageEntry` in the manifest (if one exists) unless
`shouldUpdate` is true. Otherwise, produces the package based on `url` and `rev`
and saves the result to the manifest.
-/
def materializeGitPkg (name : String) (dir : FilePath)
(url : String) (rev? : Option String) (shouldUpdate := true) : ResolveM PUnit := do
  let repo := GitRepo.mk dir
  if let some entry := (← get).find? name then
    if shouldUpdate then
      if (← repo.dirExists) then
        if url = entry.url then
          if shouldUpdate then
            updateGitPkg repo rev?
        else
          logInfo s!"{name}: URL changed, deleting {dir} and cloning again"
          IO.FS.removeDirAll dir
          cloneGitPkg repo url rev?
      else
        cloneGitPkg repo url rev?
      let rev ← repo.headRevision
      modify (·.insert name {entry with url, rev})
    else
      if (← repo.dirExists) then
        if url = entry.url then
          updateGitPkg repo entry.rev
      else
        cloneGitPkg repo entry.url entry.rev
  else
    if (← repo.dirExists) then
      if shouldUpdate then
        logInfo s!"{name}: no manifest entry, deleting {dir} and cloning again"
        IO.FS.removeDirAll dir
        cloneGitPkg repo url rev?
    else
      cloneGitPkg repo url rev?
    let rev ← repo.headRevision
    modify (·.insert name {name, url, rev})

/--
Materializes a `Dependency` relative to the given `Package`,
downloading and/or updating it as necessary.
-/
def materializeDep (ws : Workspace)
(pkg : Package) (dep : Dependency) (shouldUpdate := true) : ResolveM FilePath :=
  match dep.src with
  | Source.path dir => return pkg.dir / dir
  | Source.git url rev? subDir? => do
    let name := dep.name.toString (escape := false)
    let gitDir := ws.packagesDir / name
    materializeGitPkg name gitDir url rev? shouldUpdate
    return match subDir? with | some subDir => gitDir / subDir | none => gitDir

/--
Resolves a `Dependency` relative to the given `Package`
in the same `Workspace`, downloading and/or updating it as necessary.
-/
def resolveDep (ws : Workspace)
(pkg : Package) (dep : Dependency) (shouldUpdate := true) : ResolveM Package := do
  let dir ← materializeDep ws pkg dep shouldUpdate
  let depPkg ← Package.load dir dep.options
  unless depPkg.name == dep.name do
    throw <| IO.userError <|
      s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
      s!"but resolved dependency has name {depPkg.name} (in {depPkg.dir})"
  return depPkg

/--
Resolves the package's dependencies,
downloading and/or updating them as necessary.
-/
def resolveDeps (ws : Workspace) (pkg : Package)
(shouldUpdate := true) : ResolveM (NameMap Package) := do
  let resolve dep resolve := do
    let pkg ← resolveDep ws pkg dep shouldUpdate
    pkg.dependencies.forM fun dep => discard <| resolve dep
    return pkg
  let (res, map) ← EStateT.run (mkRBMap _ _ Lean.Name.quickCmp) <|
    pkg.dependencies.forM fun dep => discard <| buildTop Dependency.name resolve dep
  match res with
  | Except.ok _ => return map
  | Except.error cycle => do
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"
