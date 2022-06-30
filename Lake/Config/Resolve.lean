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
def updateGitPkg (name : String)
(repo : GitRepo) (rev? : Option String) : LogIO PUnit := do
  if let some rev := rev? then
    if (← repo.branchExists rev) then
      repo.fetch
      let rev ← repo.parseOriginRevision rev
      if (← repo.headRevision) == rev then return
      logInfo s!"{name}: updating {repo} to revision {rev}"
      repo.checkoutDetach rev
    else
      if (← repo.headRevision) == rev then return
      logInfo s!"{name}: updating {repo} to revision {rev}"
      unless ← repo.revisionExists rev do repo.fetch
      repo.checkoutDetach rev
  else
    logInfo s!"{name}: updating {repo}"
    repo.pull

/-- Clone the Git package as `repo`. -/
def cloneGitPkg (name : String) (repo : GitRepo)
(url : String) (rev? : Option String) : LogIO PUnit := do
  logInfo s!"{name}: cloning {url} to {repo}"
  repo.clone url
  if let some rev := rev? then
    let hash ← repo.parseOriginRevision rev
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
    if (← repo.dirExists) then
      if url = entry.url then
        if shouldUpdate then
          updateGitPkg name repo rev?
          let rev ← repo.headRevision
          modify (·.insert name {entry with rev})
        else
          updateGitPkg name repo entry.rev
      else if shouldUpdate then
        logInfo s!"{name}: URL changed, deleting {dir} and cloning again"
        IO.FS.removeDirAll dir
        cloneGitPkg name repo url rev?
        let rev ← repo.headRevision
        modify (·.insert name {entry with url, rev})
    else
      if shouldUpdate then
        cloneGitPkg name repo url rev?
        let rev ← repo.headRevision
        modify (·.insert name {entry with url, rev})
      else
        cloneGitPkg name repo entry.url entry.rev
  else
    if (← repo.dirExists) then
      let rev ← repo.headRevision
      modify (·.insert name {name, url, rev})
    else
      cloneGitPkg name repo url rev?
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
  | Source.git url rev? => do
    let name := dep.name.toString (escape := false)
    let depDir := ws.packagesDir / name
    materializeGitPkg name depDir url rev? shouldUpdate
    return depDir

/--
Resolves a `Dependency` relative to the given `Package`
in the same `Workspace`, downloading and/or updating it as necessary.
-/
def resolveDep (ws : Workspace)
(pkg : Package) (dep : Dependency) (shouldUpdate := true) : ResolveM Package := do
  let dir ← materializeDep ws pkg dep shouldUpdate
  let depPkg ← Package.load (dir / dep.dir) dep.args
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
