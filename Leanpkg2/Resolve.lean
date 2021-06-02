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

def materialize (relPath : FilePath) (dep : Dependency) : IO FilePath :=
  match dep.src with
  | Source.path dir => do
    let depdir := relPath / dir
    IO.eprintln s!"{dep.name}: using local path {depdir}"
    depdir
  | Source.git url rev branch => do
    let depdir := depsPath / dep.name
    materializeGit dep.name depdir url rev branch
    depdir

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

def solveDepsCore
  (pkgName : String) (relPath : FilePath) (deps : List Dependency)
: (maxDepth : Nat) → Solver Unit
  | 0 => throw <| IO.userError "maximum dependency resolution depth reached"
  | maxDepth + 1 => do
    let newDeps ← deps.filterM (notYetAssigned ·.name)
    for dep in newDeps do
      let dir ← materialize relPath dep
      let m ← Manifest.fromTomlFile <| dir / leanpkgToml
      modify (·.insert dep.name ⟨dir, m⟩)
    for dep in newDeps do
      let depPkg ← resolvedPackage dep.name
      unless depPkg.name = dep.name do
        throw <| IO.userError s!"{pkgName} (in {relPath}) depends on {depPkg.name}, but resolved dependency has name {dep.name} (in {depPkg.dir})"
      solveDepsCore depPkg.name depPkg.dir depPkg.dependencies maxDepth

def solveDeps (m : Manifest) : IO (List Package) := do
  let solver := solveDepsCore m.name ⟨"."⟩ m.dependencies 1024
  let (_, assg) ← solver.run (Assignment.empty.insert m.name ⟨".", m⟩)
  assg.reverse.mapM (·.2)
