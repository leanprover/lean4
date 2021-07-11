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

abbrev FileTarget := MTimeBuildTarget FilePath

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

protected def LeanArtifact.getMTime (self : LeanArtifact) : IO MTime := do
  return max (← getMTime self.oleanFile) (← getMTime self.cFile)

instance : GetMTime LeanArtifact := ⟨LeanArtifact.getMTime⟩

abbrev LeanTarget := MTimeBuildTarget LeanArtifact

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

abbrev PackageTarget :=  MTimeBuildTarget (Package × NameMap LeanTarget)

namespace PackageTarget

def package (self : PackageTarget) := self.artifact.1
def moduleTargets (self : PackageTarget) : NameMap LeanTarget :=
  self.artifact.2

end PackageTarget

-- # Build Components

def catchErrors (action : IO PUnit) : IO PUnit := do
  try action catch e =>
    -- print compile errors early
    IO.eprintln e
    throw e

def skipIfNewer [GetMTime a]
(artifact : a) (depMTime : MTime) (build : IO BuildTask)
: IO (MTimeBuildTarget a) := do
  -- construct a nop target if we have an up-to-date file
  try
    if (← getMTime artifact) >= depMTime then
      return MTimeBuildTarget.pure artifact depMTime
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e => throw e
  -- otherwise construct a proper target
  return MTimeBuildTarget.mk artifact depMTime (← build)

def fetchLeanTarget (leanFile oleanFile cFile : FilePath)
(importTargets : List LeanTarget) (depsTarget : MTimeBuildTarget PUnit)
(leanPath : String := "") (rootDir : FilePath := ".") (leanArgs : Array String := #[])
: IO LeanTarget := do
  -- calculate max dependency `MTime`
  let leanMTime ← getMTime leanFile
  let importMTimes := importTargets.map (·.mtime)
  let depMTime := MTime.listMax <| leanMTime :: depsTarget.mtime :: importMTimes
  -- construct a nop target if we have an up-to-date .olean and .c
  let depTargets := depsTarget.withArtifact arbitrary :: importTargets
  skipIfNewer ⟨oleanFile, cFile⟩ depMTime <|
    BuildTask.afterTargets depTargets <| catchErrors <|
      compileOleanAndC leanFile oleanFile cFile leanPath rootDir leanArgs

def buildO (oFile : FilePath)
(cTarget : FileTarget) (leancArgs : Array String := #[]) : IO BuildTask :=
  BuildTask.afterTarget cTarget <| catchErrors <|
    compileO oFile cTarget.artifact leancArgs

def fetchOFileTarget (oFile : FilePath)
(cTarget : FileTarget) (leancArgs : Array String := #[]) : IO FileTarget :=
  -- construct a nop target if we have an up-to-date .o
  skipIfNewer oFile cTarget.mtime <| buildO oFile cTarget leancArgs

-- # Topological Builder

/-- A recursive object fetcher. -/
def RecFetch.{u,v,w} (k : Type u) (o : Type v) (m : Type v → Type w) :=
  k → (k → m o) → m o

/-- Monad transformer for an RBMap-based topological builder. -/
abbrev RBTopT.{u,v} (k : Type u) (o : Type u) (cmp) (m : Type u → Type v) :=
  StateT (Std.RBMap k o cmp) <| ExceptT (List k) m

/-- An RBMap-based topological fetch. -/
def RBTopFetch.{u,v} (k : Type u) (o : Type u) (cmp) (m : Type u → Type v) :=
  RecFetch k o (RBTopT (cmp := cmp) k o m)

/-- Recursively builds a RBMao of key-object pairs topologically. -/
partial def buildRBTopCore
{k o} {cmp} {m : Type u → Type u} [BEq k] [Inhabited o] [Monad m]
(parents : List k) (key : k) (fetch : RecFetch k o (RBTopT (cmp := cmp) k o m))
: RBTopT (cmp := cmp) k o m o := do
  -- detect cyclic builds
  if parents.contains key then
    throw <| key :: (parents.partition (· != key)).1 ++ [key]

  -- return previous output if already built
  if let some output := (← get).find? key then
    return output

  -- build the key recursively
  let output ← fetch key fun depKey =>
    buildRBTopCore (key :: parents) depKey fetch

  -- save output (to prevent repeated builds of the same key)
  modify (·.insert key output)
  return output

def buildRBTop
{k o} {cmp} {m : Type u → Type u} [BEq k] [Inhabited o] [Monad m]
(key : k) (fetch : RecFetch k o (RBTopT (cmp := cmp) k o m)) :=
  buildRBTopCore [] key fetch

-- # Build Modules

def parseDirectLocalImports (root : Name) (leanFile : FilePath) : IO (List Name) := do
  let contents ← IO.FS.readFile leanFile
  let (imports, _, _) ← Elab.parseImports contents leanFile.toString
  imports.map (·.module) |>.filter (·.getRoot == root)

abbrev RecFetchLeanTarget (m) :=
  RecFetch Name LeanTarget m

/-
  `depsTarget` is used for external dependencies
  the module builder must wait to finish building before it can start
  ex. olean roots of dependencies
-/
def RecFetchLeanTarget.mk
(pkg : Package) (oleanDirs : List FilePath) (depsTarget : MTimeBuildTarget PUnit)
{m} [Monad m] [MonadLiftT IO m] : RecFetchLeanTarget m :=
  let leanPath := SearchPath.toString <| pkg.oleanDir :: oleanDirs
  fun mod fetch => do
    let leanFile := pkg.modToSource mod
    let imports ← parseDirectLocalImports pkg.module leanFile
    let importTargets ← imports.mapM fetch
    fetchLeanTarget leanFile (pkg.modToOlean mod) (pkg.modToC mod)
      importTargets depsTarget leanPath pkg.dir pkg.leanArgs

/-
  Equivalent to `RBTopT (cmp := Name.quickCmp) Name LeanTarget IO`
  Phrased this way to uses `NameMap`
-/
abbrev LeanTargetM :=
  StateT (NameMap LeanTarget) <| ExceptT (List Name) IO

abbrev RecLeanTargetM :=
  ReaderT (RecFetchLeanTarget LeanTargetM) LeanTargetM

def buildModule (mod : Name) : RecLeanTargetM LeanTarget :=
  fun fetch => buildRBTop mod fetch

def RecLeanTargetM.run
(pkg : Package) (oleanDirs : List FilePath)
(depsTarget : MTimeBuildTarget PUnit) (self : RecLeanTargetM α)
: IO (α × NameMap LeanTarget) := do
  let fetch := RecFetchLeanTarget.mk pkg oleanDirs depsTarget
  let res ← ReaderT.run self fetch |>.run {} |>.run
  match res with
  | Except.ok res => res
  | Except.error cycle =>
    let cycle := cycle.map (s!"  {·}")
    throw <| IO.userError s!"import cycle detected:\n{"\n".intercalate cycle}"

-- # Configure/Build Packages

def Package.buildTargetWithDepTargets
(depTargets : List PackageTarget) (self : Package)
: IO PackageTarget := do
  let depsTarget ← MTimeBuildTarget.all depTargets
  let depOLeanDirs := depTargets.map (·.package.oleanDir)
  let (target, targetMap) ← buildModule self.module
    |>.run self depOLeanDirs depsTarget
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

-- # Print Paths

def Package.buildModuleTargetsWithDeps
(deps : List Package) (mods : List Name)  (self : Package)
: IO (List LeanTarget) := do
  let oleanDirs := deps.map (·.oleanDir)
  let depsTarget ← MTimeBuildTarget.all (← deps.mapM (·.buildTarget))
  let (targets, _) ← mods.mapM buildModule |>.run self oleanDirs depsTarget
  targets

def Package.buildModulesWithDeps
(deps : List Package) (mods : List Name)  (self : Package)
: IO PUnit := do
  let targets ← self.buildModuleTargetsWithDeps deps mods
  let tasks ← targets.mapM (·.buildTask)
  for task in tasks do
    try task.await catch e =>
      -- actual error has already been printed within target
      throw <| IO.userError "Build failed."

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← solveDeps pkg
  unless imports.isEmpty do
    let imports := imports.map (·.toName)
    let localImports := imports.filter (·.getRoot == pkg.module)
    pkg.buildModulesWithDeps deps localImports
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.sourceDir :: deps.map (·.sourceDir)

-- # Build Package Lib

def PackageTarget.fetchOFileTargets
(self : PackageTarget) : IO (List FileTarget) := do
  self.moduleTargets.toList.mapM fun (mod, target) => do
    let oFile := self.package.modToO mod
    fetchOFileTarget oFile target.cTarget self.package.leancArgs

def PackageTarget.buildStaticLib
(self : PackageTarget) : IO BuildTask := do
  let oFileTargets ← self.fetchOFileTargets
  let oFiles := oFileTargets.map (·.artifact) |>.toArray
  BuildTask.afterTargets oFileTargets <| catchErrors <|
    compileStaticLib self.package.staticLibFile oFiles

def PackageTarget.fetchStaticLibTarget
(self : PackageTarget) : IO FileTarget := do
  -- construct a nop target if we have an up-to-date lib
  skipIfNewer self.package.staticLibFile self.mtime self.buildStaticLib

def Package.fetchStaticLibTarget (self : Package) : IO FileTarget := do
  let target ← self.buildTarget
  target.fetchStaticLibTarget

def Package.fetchStaticLib (self : Package) : IO FilePath := do
  let target ← self.fetchStaticLibTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildLib (pkg : Package) : IO PUnit :=
  discard pkg.fetchStaticLib

-- # Build Package Bin

def PackageTarget.buildBin
(depTargets : List PackageTarget) (self : PackageTarget)
: IO BuildTask := do
  let binFile := self.package.binFile
  let oFileTargets ← self.fetchOFileTargets
  let oFiles := oFileTargets.map (·.artifact) |>.toArray
  let libTargets ← depTargets.mapM (·.fetchStaticLibTarget)
  let libFiles := libTargets.map (·.artifact) |>.toArray
  let buildTask ← BuildTask.afterTargets oFileTargets <| catchErrors <|
    compileBin binFile (oFiles ++ libFiles) self.package.linkArgs
  return buildTask

def PackageTarget.fetchBinTarget
(depTargets : List PackageTarget) (self : PackageTarget) : IO FileTarget :=
  -- construct a nop target if we have an up-to-date bin
  skipIfNewer self.package.binFile self.mtime <| self.buildBin depTargets

def Package.fetchBinTarget (self : Package) : IO FileTarget := do
  let depTargets ← self.buildDepTargets
  let pkgTarget ← self.buildTargetWithDepTargets depTargets
  pkgTarget.fetchBinTarget depTargets

def Package.fetchBin (self : Package) : IO FilePath := do
  let target ← self.fetchBinTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildBin (pkg : Package) : IO PUnit :=
  discard pkg.fetchBin
