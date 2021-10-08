/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Git
import Lake.LeanConfig

open System

namespace Lake

open Git in
/--
  Materializes a Git package in the given `dir`,
  cloning and/or updating it as necessary.
-/
def materializeGit
(name : String) (dir : FilePath) (url rev : String) (branch : Option String)
: IO Unit := do
  if ← dir.isDir then
    IO.eprint s!"{name}: trying to update {dir} to revision {rev}"
    IO.eprintln (match branch with | none => "" | some branch => "@" ++ branch)
    let hash ← parseOriginRevision rev dir
    unless ← revisionExists hash dir do fetch dir
    checkoutDetach hash dir
  else
    IO.eprintln s!"{name}: cloning {url} to {dir}"
    clone url dir
    let hash ← parseOriginRevision rev dir
    checkoutDetach hash dir

/--
  Materializes a `Dependency` relative to the given `Package`,
  downloading and/or updating it as necessary.
-/
def materializeDep (pkg : Package) (dep : Dependency) : IO FilePath :=
  match dep.src with
  | Source.path dir => pkg.dir / dir
  | Source.git url rev branch => do
    let name := dep.name.toString (escape := false)
    let depDir := pkg.depsDir / name
    materializeGit name depDir url rev branch
    depDir

/--
  Resolves a `Dependency` relative to the given `Package`
  in the same `Workspace`, downloading and/or updating it as necessary.
-/
def resolveDep (pkg : Package) (dep : Dependency) : IO Package := do
  let dir ← materializeDep pkg dep
  let depPkg ← Package.load (dir / dep.dir) dep.args
  unless depPkg.name == dep.name do
    throw <| IO.userError <|
      s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
      s!"but resolved dependency has name {depPkg.name} (in {depPkg.dir})"
  return depPkg.withWorkspace pkg.workspace

/--
  Resolves the package's direct dependencies,
  downloading and/or updating them as necessary.
-/
def Package.resolveDirectDeps (self : Package) : IO (Array Package) :=
  self.dependencies.mapM (resolveDep self ·)
