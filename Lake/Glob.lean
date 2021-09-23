/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Lean.Data.Name
import Lean.Elab.Import

open System (FilePath)
open Lean (Name)

namespace Lake

/--
  A specification of a set of module names to build.
-/
inductive Glob
  | /-- Builds the specified module name -/
    one : Name → Glob
  | /-- Builds the specified module and all submodules -/
    andSubdirs : Name → Glob
  | /--
      Builds all submodules of the specified module,
      without building the module itself
    -/
    subdirs : Name → Glob

instance : Coe Name Glob := ⟨Glob.one⟩

-- TODO(Mario): Rename Lean.modToFilePath.go to modToDir
def modToDir (base : FilePath) : Name → FilePath
  | Name.str p h _ => modToDir base p / h
  | Name.anonymous => base
  | Name.num p _ _ => panic! "ill-formed import"

partial def directoryTraversal [Monad m] [MonadLiftT IO m]
  (base : FilePath) (push : FilePath → m PUnit) : m PUnit := do
  for entry in ← base.readDir do
    let path := entry.path
    if (← path.isDir : Bool) then
      directoryTraversal path push
    else
      push path

def onSubdirectoryFilesWithExt [Monad m] [MonadLiftT IO m]
  (base : FilePath) (ext : String) (push : FilePath → m PUnit) : m PUnit :=
  directoryTraversal base fun file => do
    if file.extension == some ext then
      push file

def Glob.pushFilePaths [Monad m] [MonadLiftT IO m]
  (base : FilePath) (ext : String) (push : FilePath → m PUnit) :
  Glob → m PUnit
  | Glob.one n => push $ modToDir base n |>.withExtension ext
  | Glob.subdirs n =>
    let dir := modToDir base n
    onSubdirectoryFilesWithExt base ext push
  | Glob.andSubdirs n => do
    let dir := modToDir base n
    onSubdirectoryFilesWithExt base ext push
    push $ dir.withExtension ext

def globsToFilePaths (base : FilePath) (ext : String)
  (globs : List Glob) : IO (Array FilePath) := do
  let arr ← IO.mkRef #[]
  for glob in globs do
    glob.pushFilePaths base ext fun file => arr.modify (·.push file)
  arr.get
