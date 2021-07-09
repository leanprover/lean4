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

abbrev FileBuildTarget := BuildTarget FilePath

structure LeanArtifact where
  oleanFile : FilePath
  cFile : FilePath
  deriving Inhabited

abbrev LeanBuildTarget := BuildTarget LeanArtifact

namespace LeanBuildTarget

def oleanFile (self : LeanBuildTarget) := self.artifact.oleanFile
def oleanTarget (self : LeanBuildTarget) : FileBuildTarget :=
  {self with artifact := self.oleanFile}

def cFile (self : LeanBuildTarget) := self.artifact.cFile
def cTarget (self : LeanBuildTarget) : FileBuildTarget :=
  {self with artifact := self.cFile}

end LeanBuildTarget

def buildOleanAndC (leanFile oleanFile cFile : FilePath) 
(depTargets : List LeanBuildTarget) (moreDepsMTime : IO.FS.SystemTime) 
(leanPath : String := "") (rootDir : FilePath := ".") (leanArgs : Array String := #[])
: IO LeanBuildTarget := do
  let artifact := ⟨oleanFile, cFile⟩
  -- calculate transitive `maxMTime`
  let leanMData ← leanFile.metadata
  let depMTimes ← depTargets.mapM (·.maxMTime)
  let maxMTime := List.maximum? (leanMData.modified :: moreDepsMTime :: depMTimes) |>.get!
  -- construct a nop target if we have an up-to-date .olean and .c
  try
    let cMTime := (← cFile.metadata).modified
    let oleanMTime := (← oleanFile.metadata).modified
    if cMTime >= maxMTime && oleanMTime >= maxMTime then
      return BuildTarget.pure artifact maxMTime
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e                             => throw e
  -- construct a proper target otherwise
  let buildTask ← BuildTask.afterTargets depTargets do
    try
      compileOleanAndC leanFile oleanFile cFile leanPath rootDir leanArgs
    catch e =>
      -- print compile errors early
      IO.eprintln e
      throw e
  return { artifact, maxMTime, buildTask }

def buildO (oFile : FilePath) 
(cTarget : FileBuildTarget) (leancArgs : Array String := #[]) 
: IO FileBuildTarget := do
  -- construct a nop target if we have an up-to-date .o
  let cMTime := cTarget.maxMTime
  try 
    if (← oFile.metadata).modified >= cMTime then 
      return BuildTarget.pure oFile cMTime
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e => throw e
  -- construct a proper target otherwise
  let buildTask ← cTarget.afterBuild do
    try
      compileO oFile cTarget.artifact leancArgs
    catch e =>
      -- print compile errors early
      IO.eprintln e
      throw e
  return {artifact := oFile, maxMTime := cMTime, buildTask}

-- # Build Modules

structure ModuleTargetContext where
  package       : Package
  leanPath      : String
  buildParents  : List Name := []
  -- things that should also trigger rebuilds
  -- ex. olean roots of dependencies
  moreDeps      : List FilePath
  moreDepsMTime : IO.FS.SystemTime

abbrev ModuleTargetM :=
   ReaderT ModuleTargetContext <| StateT (NameMap LeanBuildTarget) IO

partial def buildTargetsForModule (mod : Name) : ModuleTargetM LeanBuildTarget := do
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
  let depTargets ← directLocalImports.mapM fun i =>
    withReader (fun ctx => { ctx with buildParents := mod :: ctx.buildParents }) <|
      buildTargetsForModule i

  -- do build
  let cFile := pkg.modToC mod
  let oleanFile := pkg.modToOlean mod
  let target ← buildOleanAndC leanFile oleanFile cFile 
    depTargets ctx.moreDepsMTime ctx.leanPath pkg.dir pkg.leanArgs
  modify (·.insert mod target)
  return target

def mkModuleTargetContext 
(pkg : Package) (deps : List Package) : IO ModuleTargetContext := do
  let moreDeps := deps.map (·.oleanRoot)
  let moreDepsMTime := (← moreDeps.mapM (·.metadata)).map (·.modified) |>.maximum? |>.getD ⟨0, 0⟩
  let leanPath := SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  return { package := pkg, leanPath, moreDeps, moreDepsMTime }

def buildPackageModuleTargetMap 
(pkg : Package) (deps : List Package) : IO (NameMap LeanBuildTarget) := do
  let crx ← mkModuleTargetContext pkg deps
  let (_, targetMap) ← buildTargetsForModule pkg.module |>.run crx |>.run {}
  return targetMap

def buildPackageModules 
(pkg : Package) (deps : List Package) : IO PUnit := do
  let crx ← mkModuleTargetContext pkg deps
  let target ← buildTargetsForModule pkg.module |>.run crx |>.run' {}
  try target.materialize catch _ =>
    -- actual error has already been printed within buildTask
    throw <| IO.userError "Build failed."

def buildModulesInPackage 
(pkg : Package) (deps : List Package) (mods : List Name) : IO Unit := do
  let ctx ← mkModuleTargetContext pkg deps
  let targets ← mods.mapM buildTargetsForModule |>.run ctx |>.run' {}
  let tasks ← targets.mapM (·.buildTask)
  for task in tasks do
    try task.await catch e =>
      -- actual error has already been printed within buildTask
      throw <| IO.userError "Build failed."

-- # Configure/Build Packages

def buildDeps (pkg : Package) : IO (List Package) := do
  let deps ← solveDeps pkg
  for dep in deps do
    -- build recursively
    -- TODO: share build of common dependencies
    let depDeps ← solveDeps dep
    buildPackageModules pkg deps
  return deps

def configure (pkg : Package) : IO Unit := do
  discard <| buildDeps pkg

def build (pkg : Package) : IO Unit := do
  let deps ← buildDeps pkg
  buildPackageModules pkg deps

-- # Build Package Lib/Bin

def buildPackageOFiles 
(pkg : Package) (targetMap : NameMap LeanBuildTarget)
: IO (List FilePath) := do 
  let oTasks ← targetMap.toList.mapM fun (mod, target) => do
    let oFile := pkg.modToO mod
    let target ← buildO oFile target.cTarget pkg.leancArgs
    (oFile, ← target.buildTask)
  oTasks.mapM fun (oFile, task) => do
    task.await
    oFile

def buildStaticLib (pkg : Package) : IO FilePath := do
  let deps ← buildDeps pkg
  let targetMap ← buildPackageModuleTargetMap pkg deps
  let oFiles ← buildPackageOFiles pkg targetMap
  compileLib pkg.staticLibFile oFiles.toArray
  pkg.staticLibFile

def buildBin (pkg : Package) : IO FilePath := do
  let deps ← solveDeps pkg
  let depLibs ← deps.mapM buildStaticLib
  let targetMap ← buildPackageModuleTargetMap pkg deps
  let oFiles ← buildPackageOFiles pkg targetMap
  compileBin pkg.binFile (oFiles ++ depLibs).toArray pkg.linkArgs
  pkg.binFile

-- # Print Paths

def buildImports 
(pkg : Package) (deps : List Package) (imports : List String := []) 
: IO Unit := do
  let imports := imports.map (·.toName)
  let localImports := imports.filter (·.getRoot == pkg.module)
  buildModulesInPackage pkg deps localImports

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← buildDeps pkg
  buildImports pkg deps imports
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.sourceDir :: deps.map (·.sourceDir)

