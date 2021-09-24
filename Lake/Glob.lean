/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Mac Malone
-/
import Lean.Data.Name

open Lean (Name)
open System (FilePath)

namespace Lake

/-- A specification of a set of module names. -/
inductive Glob
| /-- Selects the specified module name. -/
  one : Name → Glob
| /--
    Selects all submodules of the specified module,
    without building the module itself.
  -/
  submodules : Name → Glob
| /-- Selects the specified module and all submodules. -/
  andSubmodules : Name → Glob

instance : Coe Name Glob := ⟨Glob.one⟩

def Glob.matches (m : Name) : (self : Glob) → Bool
| one n => n == m
| submodules n => n.isPrefixOf m
| andSubmodules n => n == m || n.isPrefixOf m

-- TODO(Mario): Rename Lean.modToFilePath.go to modToDir
def modToDir (base : FilePath) : Name → FilePath
  | Name.str p h _ => modToDir base p / h
  | Name.anonymous => base
  | Name.num p _ _ => panic! "ill-formed import"

partial def pushSubmodules
(dir : FilePath) (root : Name) (arr : Array Name) : IO (Array Name) := do
  let mut arr := arr
  let dirPath := modToDir dir root
  for entry in (← dirPath.readDir) do
    let path := entry.path
    if (← path.isDir : Bool) then
      arr ← pushSubmodules path (root ++ entry.fileName) arr
    else if path.extension == some "lean" then
      let fileName := FilePath.withExtension entry.fileName "" |>.toString
      arr := arr.push (root ++ fileName)
  return arr

def Glob.pushModules (dir : FilePath) (arr : Array Name)
: (self : Glob) → IO (Array Name)
| one n => #[n]
| submodules n => pushSubmodules dir n arr
| andSubmodules n => pushSubmodules dir n (arr.push n)

def Glob.getModules (dir : FilePath)  (self : Glob) :=
  pushModules dir #[]
