/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Mac Malone
-/
import Lean.Util.Path
import Lake.Util.Name

open Lean (Name)
open System (FilePath)

namespace Lake

/-- A specification of a set of module names. -/
inductive Glob
  /-- Selects just the specified module name. -/
  | one : Name → Glob
  /-- Selects all submodules of the specified module, but not the module itself. -/
  | submodules : Name → Glob
  /-- Selects the specified module and all submodules. -/
  | andSubmodules : Name → Glob
deriving Inhabited, Repr

instance : Coe Name Glob := ⟨Glob.one⟩

partial def forEachModuleIn [Monad m] [MonadLiftT IO m]
(dir : FilePath) (f : Name → m PUnit) (ext := "lean") : m PUnit := do
  for entry in (← dir.readDir) do
    if (← liftM (m := IO) <| entry.path.isDir) then
      let n := Name.mkSimple entry.fileName
      let r := FilePath.withExtension entry.fileName ext
      if (← liftM (m := IO) r.pathExists) then f n
      forEachModuleIn entry.path (f <| n ++ ·)
    else if entry.path.extension == some ext then
      f <| Name.mkSimple <| FilePath.withExtension entry.fileName "" |>.toString

namespace Glob

def «matches» (m : Name) : (self : Glob) → Bool
| one n => n == m
| submodules n => n.isPrefixOf m && n != m
| andSubmodules n => n.isPrefixOf m

@[inline] nonrec def forEachModuleIn [Monad m] [MonadLiftT IO m]
(dir : FilePath) (f : Name → m PUnit) : (self : Glob) → m PUnit
| one n => f n
| submodules n =>
  forEachModuleIn (Lean.modToFilePath dir n "") (f <| n ++ ·)
| andSubmodules n =>
  f n *> forEachModuleIn (Lean.modToFilePath dir n "") (f <| n ++ ·)
