/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Util.Git
import Lake.Config.Load
import Lake.Config.Workspace

open System

namespace Lake

open Git in
/--
Materializes a Git package in the given `dir`,
cloning and/or updating it as necessary.
-/
def materializeGit
(name : String) (dir : FilePath) (url rev : String) : (LogT IO) PUnit := do
  if ← dir.isDir then
    logInfo s!"{name}: trying to update {dir} to revision {rev}"
    let hash ← parseOriginRevision rev dir
    unless ← revisionExists hash dir do fetch dir
    checkoutDetach hash dir
  else
    logInfo s!"{name}: cloning {url} to {dir}"
    clone url dir
    let hash ← parseOriginRevision rev dir
    checkoutDetach hash dir

/--
Materializes a `Dependency` relative to the given `Package`,
downloading and/or updating it as necessary.
-/
def materializeDep (ws : Workspace) (pkg : Package) (dep : Dependency) : (LogT IO) FilePath :=
  match dep.src with
  | Source.path dir => pkg.dir / dir
  | Source.git url rev => do
    let name := dep.name.toString (escape := false)
    let depDir := ws.depsDir / name
    materializeGit name depDir url rev
    depDir

/--
Resolves a `Dependency` relative to the given `Package`
in the same `Workspace`, downloading and/or updating it as necessary.
-/
def resolveDep (ws : Workspace) (pkg : Package) (dep : Dependency) : (LogT IO) Package := do
  let dir ← materializeDep ws pkg dep
  let depPkg ← Package.load (dir / dep.dir) dep.args
  unless depPkg.name == dep.name do
    throw <| IO.userError <|
      s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
      s!"but resolved dependency has name {depPkg.name} (in {depPkg.dir})"
  return depPkg

/--
Resolves the package's direct dependencies,
downloading and/or updating them as necessary.
-/
def resolveDirectDeps (ws : Workspace) (self : Package) : (LogT IO) (Array Package) :=
  self.dependencies.mapM (resolveDep ws self ·)
