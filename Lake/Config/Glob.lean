/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Mac Malone
-/
import Lean.Util.Path

open Lean (Name)
open System (FilePath)

namespace Lake

/-- A specification of a set of module names. -/
inductive Glob
| /-- Selects just the specified module name. -/
  one : Name → Glob
| /-- Selects all submodules of the specified module, but not the module itself. -/
  submodules : Name → Glob
| /-- Selects the specified module and all submodules. -/
  andSubmodules : Name → Glob
deriving Inhabited, Repr

instance : Coe Name Glob := ⟨Glob.one⟩

def Glob.matches (m : Name) : (self : Glob) → Bool
| one n => n == m
| submodules n => n.isPrefixOf m && n != m
| andSubmodules n => n.isPrefixOf m

partial def pushSubmodules
(rootDir : FilePath) (mod : Name) (arr : Array Name) : IO (Array Name) := do
  let mut arr := arr
  let dirPath := Lean.modToFilePath rootDir mod ""
  for entry in (← dirPath.readDir) do
    let path := entry.path
    if (← path.isDir) then
      arr ← pushSubmodules rootDir (mod ++ entry.fileName) arr
    else if path.extension == some "lean" then
      let fileName := FilePath.withExtension entry.fileName "" |>.toString
      arr := arr.push (mod ++ fileName)
  return arr

def Glob.pushModules
(dir : FilePath) (arr : Array Name) : (self : Glob) → IO (Array Name)
| one n => pure #[n]
| submodules n => pushSubmodules dir n arr
| andSubmodules n => pushSubmodules dir n (arr.push n)

def Glob.getModules (dir : FilePath) (self : Glob) : IO (Array Name) :=
  self.pushModules dir #[]
