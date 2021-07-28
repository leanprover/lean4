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

def materialize (pkg : Package) (dep : Dependency) : IO FilePath :=
  match dep.src with
  | Source.path dir => do
    let depDir := pkg.dir / dir
    depDir
  | Source.git url rev branch => do
    let depDir := pkg.depsDir / dep.name
    materializeGit dep.name depDir url rev branch
    depDir

def Assignment := List (String × Package)

namespace Assignment

def empty : Assignment := []

def contains (a : Assignment) (s : String) : Bool :=
  (a.lookup s).isSome

def insert (a : Assignment) (k : String) (v : Package) : Assignment :=
  if a.contains k then a else (k, v) :: a

def fold {α} (i : α) (f : α → String → Package → α) : Assignment → α :=
  List.foldl (fun a ⟨k, v⟩ => f a k v) i

end Assignment

abbrev Solver := StateT Assignment IO

def notYetAssigned (d : String) : Solver Bool := do
  ¬ (← get).contains d

def resolvedPackage (d : String) : Solver Package := do
  let some pkg ← pure ((← get).lookup d) | unreachable!
  pkg

def solveDepsCore (pkg : Package) : (maxDepth : Nat) → Solver Unit
  | 0 => throw <| IO.userError "maximum dependency resolution depth reached"
  | maxDepth + 1 => do
    let newDeps ← pkg.dependencies.filterM (notYetAssigned ·.name)
    for dep in newDeps do
      let dir ← materialize pkg dep
      let pkg ← Package.fromDir (dir / dep.dir) dep.args
      modify (·.insert dep.name pkg)
    for dep in newDeps do
      let depPkg ← resolvedPackage dep.name
      unless depPkg.name = dep.name do
        throw <| IO.userError <|
          s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
          s!"but resolved dependency has name {depPkg.name} (in {depPkg.dir})"
      solveDepsCore depPkg maxDepth

/--
  Resolves the dependency tree for the given package,
  downloading and/or updating missing dependencies as necessary.
-/
def solveDeps (pkg : Package) : IO (List Package) := do
  let solver := solveDepsCore pkg 1024
  let (_, assg) ← solver.run (Assignment.empty.insert pkg.name ⟨pkg.dir, pkg.config⟩)
  assg.reverse.tail!.mapM (·.2)
