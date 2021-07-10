/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.BuildTarget
import Lake.Resolve
import Lake.Package
import Lake.Compile

open System
open Lean hiding SearchPath

namespace Lake

-- # Build Targets

abbrev FileTarget := BuildTarget FilePath

namespace FileTarget

def mk (file : FilePath) (maxMTime : IO.FS.SystemTime) (task : BuildTask) :=
  BuildTarget.mk file maxMTime task

def pure (file : FilePath) (maxMTime : IO.FS.SystemTime) :=
  BuildTarget.pure file maxMTime

end FileTarget

structure LeanArtifact where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited

abbrev LeanTarget := BuildTarget LeanArtifact

namespace LeanTarget

def mk (olean c : FilePath) (maxMTime : IO.FS.SystemTime) (task : BuildTask) : LeanTarget :=
  BuildTarget.mk ⟨olean, c⟩ maxMTime task

def pure (olean c : FilePath) (maxMTime : IO.FS.SystemTime) : LeanTarget :=
  BuildTarget.pure ⟨olean, c⟩ maxMTime

def oleanFile (self : LeanTarget) := self.artifact.oleanFile
def oleanTarget (self : LeanTarget) : FileTarget :=
  {self with artifact := self.oleanFile}

def cFile (self : LeanTarget) := self.artifact.cFile
def cTarget (self : LeanTarget) : FileTarget :=
  {self with artifact := self.cFile}

end LeanTarget

def catchErrors (action : IO PUnit) : IO PUnit := do
  try action catch e =>
    -- print compile errors early
    IO.eprintln e
    throw e

def buildOleanAndC (leanFile oleanFile cFile : FilePath)
(importTargets : List LeanTarget) (depsTarget : BuildTarget PUnit)
(leanPath : String := "") (rootDir : FilePath := ".") (leanArgs : Array String := #[])
: IO LeanTarget := do
  -- calculate transitive `maxMTime`
  let leanMData ← leanFile.metadata
  let impMTimes ← importTargets.mapM (·.maxMTime)
  let maxMTime := List.maximum?
    (leanMData.modified :: depsTarget.maxMTime :: impMTimes) |>.get!
  -- construct a nop target if we have an up-to-date .olean and .c
  try
    let cMTime := (← cFile.metadata).modified
    let oleanMTime := (← oleanFile.metadata).modified
    if cMTime >= maxMTime && oleanMTime >= maxMTime then
      return LeanTarget.pure oleanFile cFile maxMTime
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e                             => throw e
  -- construct a proper target otherwise
  let targets := depsTarget.withArtifact arbitrary :: importTargets
  let buildTask ← BuildTask.afterTargets targets <| catchErrors <|
    compileOleanAndC leanFile oleanFile cFile leanPath rootDir leanArgs
  return LeanTarget.mk oleanFile cFile maxMTime buildTask

def buildO (oFile : FilePath)
(cTarget : FileTarget) (leancArgs : Array String := #[])
: IO FileTarget := do
  -- construct a nop target if we have an up-to-date .o
  let cMTime := cTarget.maxMTime
  try
    if (← oFile.metadata).modified >= cMTime then
      return FileTarget.pure oFile cMTime
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e => throw e
  -- construct a proper target otherwise
  let buildTask ← BuildTask.afterTarget cTarget <| catchErrors <|
    compileO oFile cTarget.artifact leancArgs
  return FileTarget.mk oFile cMTime buildTask

abbrev PackageTarget :=  BuildTarget (Package × NameMap LeanTarget)

namespace PackageTarget

def package (self : PackageTarget) := self.artifact.1
def moduleTargets (self : PackageTarget) : NameMap LeanTarget :=
  self.artifact.2

end PackageTarget

-- # Build Modules

structure LeanTargetContext where
  package      : Package
  leanPath     : String
  buildParents : List Name := []
  -- target for external dependencies
  -- ex. olean roots of dependencies
  depsTarget   : BuildTarget PUnit

abbrev LeanTargetM :=
   ReaderT LeanTargetContext <| StateT (NameMap LeanTarget) IO

partial def buildModule (mod : Name) : LeanTargetM LeanTarget := do
  let ctx ← read
  let pkg := ctx.package

  -- detect cyclic imports
  if ctx.buildParents.contains mod then
    let cycle := mod :: (ctx.buildParents.partition (· != mod)).1 ++ [mod]
    let cycle := cycle.map (s!"  {·}")
    throw <| IO.userError s!"import cycle detected:\n{"\n".intercalate cycle}"

  -- return previous result if already visited
  if let some target := (← get).find? mod then
    return target

  -- deduce lean file
  let leanFile := pkg.modToSource mod

  -- parse imports
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile leanFile) leanFile.toString
  let directLocalImports := imports.map (·.module) |>.filter (·.getRoot == pkg.module)

  -- recursively build local dependencies
  let importTargets ← directLocalImports.mapM fun i =>
    withReader (fun ctx => { ctx with buildParents := mod :: ctx.buildParents }) <|
      buildModule i

  -- do build
  let cFile := pkg.modToC mod
  let oleanFile := pkg.modToOlean mod
  let target ← buildOleanAndC leanFile oleanFile cFile
    importTargets ctx.depsTarget ctx.leanPath pkg.dir pkg.leanArgs
  modify (·.insert mod target)
  return target

def mkLeanTargetContext
(pkg : Package) (oleanDirs : List FilePath) (depsTarget : BuildTarget PUnit)
: LeanTargetContext := {
  package:= pkg
  leanPath := SearchPath.toString <| pkg.oleanDir :: oleanDirs
  depsTarget
}

-- # Configure/Build Packages

def Package.buildTargetWithDepTargets
(depTargets : List PackageTarget) (self : Package)
: IO PackageTarget := do
  let depsTarget ← BuildTarget.all depTargets
  let depOLeanDirs := depTargets.map (·.package.oleanDir)
  let ctx := mkLeanTargetContext self depOLeanDirs depsTarget
  let (target, targetMap) ← buildModule self.module |>.run ctx |>.run {}
  return {target with artifact := ⟨self, targetMap⟩}

partial def Package.buildTarget (self : Package) : IO PackageTarget := do
  let deps ← solveDeps self
  -- build dependencies recursively
  -- TODO: share build of common dependencies
  let depTargets ← deps.mapM (·.buildTarget)
  self.buildTargetWithDepTargets depTargets

def Package.buildDepTargets (self : Package) : IO (List PackageTarget) := do
  let deps ← solveDeps self
  deps.mapM (·.buildTarget)

def Package.buildDeps (self : Package) : IO (List Package) := do
  let deps ← solveDeps self
  let targets ← deps.mapM (·.buildTarget)
  try targets.forM (·.materialize) catch e =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return deps

def configure (pkg : Package) : IO Unit :=
  discard pkg.buildDeps

def Package.build (self : Package) : IO PUnit := do
  let target ← self.buildTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."

def build (pkg : Package) : IO PUnit :=
  pkg.build

-- # Build Package Lib

def PackageTarget.buildOFileTargets
(self : PackageTarget) : IO (List FileTarget) := do
  self.moduleTargets.toList.mapM fun (mod, target) => do
    let oFile := self.package.modToO mod
    buildO oFile target.cTarget self.package.leancArgs

def PackageTarget.buildStaticLibTarget
(self : PackageTarget) : IO FileTarget := do
  let libFile := self.package.staticLibFile
  -- construct a nop target if we have an up-to-date lib
  let pkgMTime := self.maxMTime
  try
    if (← libFile.metadata).modified >= pkgMTime then
      return FileTarget.pure libFile pkgMTime
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e => throw e
  -- construct a proper target otherwise
  let oFileTargets ← self.buildOFileTargets
  let oFiles := oFileTargets.map (·.artifact) |>.toArray
  let buildTask ← BuildTask.afterTargets oFileTargets <| catchErrors <|
    compileStaticLib libFile oFiles
  return FileTarget.mk libFile pkgMTime buildTask

def Package.buildStaticLibTarget (self : Package) : IO FileTarget := do
  let target ← self.buildTarget
  target.buildStaticLibTarget

def Package.buildStaticLib (self : Package) : IO FilePath := do
  let target ← self.buildStaticLibTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildLib (pkg : Package) : IO PUnit :=
  discard pkg.buildStaticLib

-- # Build Package Bin

def PackageTarget.buildBinTarget
 (depTargets : List PackageTarget) (self : PackageTarget)
: IO FileTarget := do
  let binFile := self.package.binFile
  -- construct a nop target if we have an up-to-date bin
  let pkgMTime := self.maxMTime
  try
    if (← binFile.metadata).modified >= pkgMTime then
      return FileTarget.pure binFile pkgMTime
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e => throw e
  -- construct a proper target otherwise
  let oFileTargets ← self.buildOFileTargets
  let oFiles := oFileTargets.map (·.artifact) |>.toArray
  let libTargets ← depTargets.mapM (·.buildStaticLibTarget)
  let libFiles := libTargets.map (·.artifact) |>.toArray
  let buildTask ← BuildTask.afterTargets oFileTargets <| catchErrors <|
    compileBin binFile (oFiles ++ libFiles) self.package.linkArgs
  return FileTarget.mk binFile pkgMTime buildTask

def Package.buildBinTarget (self : Package) : IO FileTarget := do
  let depTargets ← self.buildDepTargets
  let pkgTarget ← self.buildTargetWithDepTargets depTargets
  pkgTarget.buildBinTarget depTargets

def Package.buildBin (self : Package) : IO FilePath := do
  let target ← self.buildBinTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildBin (pkg : Package) : IO PUnit :=
  discard pkg.buildBin

-- # Print Paths

def buildImports
(pkg : Package) (deps : List Package) (imports : List String := [])
: IO Unit := do
  -- compute context
  let oleanDirs := deps.map (·.oleanDir)
  let depsTarget ← BuildTarget.all (← deps.mapM (·.buildTarget))
  let ctx ← mkLeanTargetContext pkg oleanDirs depsTarget
  -- build imports
  let imports := imports.map (·.toName)
  let localImports := imports.filter (·.getRoot == pkg.module)
  let targets ← imports.mapM buildModule |>.run ctx |>.run' {}
  let tasks ← targets.mapM (·.buildTask)
  for task in tasks do
    try task.await catch e =>
      -- actual error has already been printed within buildTask
      throw <| IO.userError "Build failed."

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← solveDeps pkg
  buildImports pkg deps imports
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.sourceDir :: deps.map (·.sourceDir)
