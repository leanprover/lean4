/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich
-/
import Leanpkg.Manifest
import Leanpkg.Proc
import Leanpkg.Git

open System

namespace Leanpkg

def Assignment := List (String × FilePath)

namespace Assignment
def empty : Assignment := []

def contains (a : Assignment) (s : String) : Bool :=
  (a.lookup s).isSome

def insert (a : Assignment) (k : String) (v : FilePath) : Assignment :=
  if a.contains k then a else (k, v) :: a

def fold {α} (i : α) (f : α → String → FilePath → α) : Assignment → α :=
  List.foldl (fun a ⟨k, v⟩ => f a k v) i

end Assignment

abbrev Solver := StateT Assignment IO

def notYetAssigned (d : String) : Solver Bool := do
  ¬ (← get).contains d

def resolvedPath (d : String) : Solver FilePath := do
  let some path ← pure ((← get).lookup d) | unreachable!
  path

def materialize (relpath : FilePath) (dep : Dependency) : Solver Unit :=
  match dep.src with
  | Source.path dir => do
    let depdir := dir / relpath
    IO.eprintln s!"{dep.name}: using local path {depdir}"
    modify (·.insert dep.name depdir)
  | Source.git url rev branch => do
    let depdir := FilePath.mk "build" / "deps" / dep.name
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
    modify (·.insert dep.name depdir)

def solveDepsCore (relPath : FilePath) (d : Manifest) : (maxDepth : Nat) → Solver Unit
  | 0 => throw <| IO.userError "maximum dependency resolution depth reached"
  | maxDepth + 1 => do
    let deps ← d.dependencies.filterM (notYetAssigned ·.name)
    deps.forM (materialize relPath)
    for dep in deps do
      let p ← resolvedPath dep.name
      let d' ← Manifest.fromFile $ p / "leanpkg.toml"
      unless d'.name = dep.name do
        throw <| IO.userError s!"{d.name} (in {relPath}) depends on {d'.name}, but resolved dependency has name {dep.name} (in {p})"
      solveDepsCore p d' maxDepth

def solveDeps (d : Manifest) : IO Assignment := do
  let (_, assg) ← (solveDepsCore ⟨"."⟩ d 1024).run <| Assignment.empty.insert d.name ⟨"."⟩
  assg

def constructPathCore (depname : String) (dirname : FilePath) : IO FilePath := do
  let path ← Manifest.effectivePath (← Manifest.fromFile <| dirname / leanpkgTomlFn)
  return dirname / path

def constructPath (assg : Assignment) : IO (List FilePath) := do
  assg.reverse.mapM fun ⟨depname, dirname⟩ => constructPathCore depname dirname

end Leanpkg
