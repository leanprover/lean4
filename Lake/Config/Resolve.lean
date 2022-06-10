/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Config.Load
import Lake.Config.Manifest
import Lake.Config.Workspace
import Lake.Build.Recursive

open System
open Lean (Name NameMap)

namespace Lake

section
open Git

/-- Update the Git package in `dir` to `rev` if not already at it. -/
def updateGitPkg (name : String)
(dir : FilePath) (rev? : Option String) : LogT IO PUnit := do
  if let some rev := rev? then
    if (← headRevision dir) == rev then return
    logInfo s!"{name}: updating {dir} to revision {rev}"
    unless ← revisionExists rev dir do fetch dir
    checkoutDetach rev dir
  else
    logInfo s!"{name}: updating {dir}"
    pull dir

/-- Clone the Git package as `dir`. -/
def cloneGitPkg (name : String) (dir : FilePath)
(url : String) (rev? : Option String) : LogT IO PUnit := do
  logInfo s!"{name}: cloning {url} to {dir}"
  clone url dir
  if let some rev := rev? then
    let hash ← parseOriginRevision rev dir
    checkoutDetach hash dir

abbrev ResolveM := StateT (NameMap PackageEntry) <| LogT IO

/--
Materializes a Git package in `dir`, cloning and/or updating it as necessary.

Attempts to reproduce the `PackageEntry` in the manifest (if one exists) unless
`shouldUpdate` is true. Otherwise, produces the package based on `url` and `rev`
and saves the result to the manifest.
-/
def materializeGitPkg (name : String) (dir : FilePath)
(url : String) (rev? : Option String) (shouldUpdate := true) : ResolveM PUnit := do
  if let some entry := (← get).find? name then
    if (← dir.isDir) then
      if url = entry.url then
        if shouldUpdate then
          updateGitPkg name dir rev?
          let rev ← headRevision dir
          modify (·.insert name {entry with rev})
        else
          updateGitPkg name dir entry.rev
      else if shouldUpdate then
        logInfo s!"{name}: URL changed, deleting {dir} and cloning again"
        IO.FS.removeDirAll dir
        cloneGitPkg name dir url rev?
        let rev ← headRevision dir
        modify (·.insert name {entry with url, rev})
    else
      if shouldUpdate then
        cloneGitPkg name dir url rev?
        let rev ← headRevision dir
        modify (·.insert name {entry with url, rev})
      else
        cloneGitPkg name dir entry.url entry.rev
  else
    if (← dir.isDir) then
      let rev ← headRevision dir
      modify (·.insert name {name, url, rev})
    else
      cloneGitPkg name dir url rev?
      let rev ← headRevision dir
      modify (·.insert name {name, url, rev})

end

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
  let (res, map) ← RBTopT.run <| pkg.dependencies.forM fun dep =>
    discard <| buildRBTop (cmp := Name.quickCmp) resolve Dependency.name dep
  match res with
  | Except.ok _ => return map
  | Except.error cycle => do
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"
