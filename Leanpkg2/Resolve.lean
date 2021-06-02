/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Leanpkg2.Git
import Leanpkg2.Proc
import Leanpkg2.TomlManifest
import Leanpkg2.BuildConfig

open System

namespace Leanpkg2

def depsPath := buildPath / "deps"

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

def materialize (relPath : FilePath) (dep : Dependency) : Solver Unit :=
  match dep.src with
  | Source.path dir => do
    let depdir := dir / relPath
    IO.eprintln s!"{dep.name}: using local path {depdir}"
    let m ← Manifest.fromTomlFile <| depdir / leanpkgToml
    modify (·.insert dep.name ⟨depdir, m⟩)
  | Source.git url rev branch => do
    let depdir := depsPath / dep.name
    if ← depdir.isDir then
      IO.eprint s!"{dep.name}: trying to update {depdir} to revision {rev}"
      IO.eprintln (match branch with | none => "" | some branch => "@" ++ branch)
      let hash ← gitParseOriginRevision depdir rev
      let revEx ← gitRevisionExists depdir hash
      unless revEx do
        execCmd {cmd := "git", args := #["fetch"], cwd := depdir}
    else
      IO.eprintln s!"{dep.name}: cloning {url} to {depdir}"
      execCmd {cmd := "git", args := #["clone", url, depdir.toString]}
    let hash ← gitParseOriginRevision depdir rev
    execCmd {cmd := "git", args := #["checkout", "--detach", hash], cwd := depdir}
    let m ← Manifest.fromTomlFile <| depdir / leanpkgToml
    modify (·.insert dep.name ⟨depdir, m⟩)

def solveDepsCore (pkg : String) (relPath : FilePath) (deps : List Dependency) : (maxDepth : Nat) → Solver Unit
  | 0 => throw <| IO.userError "maximum dependency resolution depth reached"
  | maxDepth + 1 => do
    let newDeps ← deps.filterM (notYetAssigned ·.name)
    newDeps.forM (materialize relPath)
    for dep in newDeps do
      let depPkg ← resolvedPackage dep.name
      unless depPkg.name = dep.name do
        throw <| IO.userError s!"{pkg} (in {relPath}) depends on {depPkg.name}, but resolved dependency has name {dep.name} (in {depPkg.dir})"
      solveDepsCore depPkg.name depPkg.dir depPkg.dependencies maxDepth

def solveDeps (m : Manifest) : IO (List Package) := do
  let (_, assg) ← (solveDepsCore m.name ⟨"."⟩ m.dependencies 1024).run <| Assignment.empty.insert m.name ⟨".", m⟩
  assg.reverse.mapM (·.2)
