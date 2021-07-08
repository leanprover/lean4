/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Resolve
import Lake.Package
import Lake.Compile

open System
open Lean hiding SearchPath

namespace Lake

-- # Basic Build Infos

structure BuildInfo (α : Type) where
  artifact  : α
  maxMTime  : IO.FS.SystemTime
  task : Task (Except IO.Error PUnit)
  deriving Inhabited

abbrev ModuleBuildInfo := BuildInfo (FilePath × FilePath)

namespace ModuleBuildInfo
def oleanFile (self : ModuleBuildInfo) := self.artifact.1
def cFile (self : ModuleBuildInfo) := self.artifact.2
end ModuleBuildInfo

def buildOleanAndC  (leanFile oleanFile cFile : FilePath) 
(depInfos : List ModuleBuildInfo) (maxMTime : IO.FS.SystemTime) 
(leanPath : String := "") (rootDir : FilePath := ".") (leanArgs : Array String := #[])
: IO ModuleBuildInfo := do
  let artifact := (oleanFile, cFile)
  -- check whether we have an up-to-date .olean and .c
  try
    let cMTime := (← cFile.metadata).modified
    let oleanMTime := (← oleanFile.metadata).modified
    if cMTime >= maxMTime && oleanMTime >= maxMTime then
      let task := Task.pure (Except.ok ())
      return { artifact, maxMTime, task }
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e                             => throw e
  -- (try to) compile the olean and c file
  let task ← IO.mapTasks (tasks := depInfos.map (·.task)) fun rs => do
    rs.forM IO.ofExcept  -- propagate first failure from dependencies
    try
      compileOleanAndC leanFile oleanFile cFile leanPath rootDir leanArgs
    catch e =>
      -- print compile errors early
      IO.eprintln e
      throw e
  return { artifact, maxMTime, task }

def buildO (oFile : FilePath) 
(cInfo : BuildInfo FilePath) (leancArgs : Array String := #[]) 
: IO (BuildInfo FilePath) := do
  -- skip if we have an up-to-date .o
  try 
    let cMTime := cInfo.maxMTime
    if (← oFile.metadata).modified >= cMTime then 
      return {artifact := oFile, maxMTime := cMTime, task := Task.pure (Except.ok ()) }
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e => throw e
  -- compile it otherwise
  let task ← IO.mapTask (t := cInfo.task) fun x => do
    IO.ofExcept x  -- propagate failure from building .c
    try
      compileO oFile cInfo.artifact leancArgs
    catch e =>
      -- print compile errors early
      IO.eprintln e
      throw e
  return {artifact := oFile, maxMTime := cInfo.maxMTime, task }

-- # Build Modules

structure BuildContext where
  package       : Package
  leanPath      : String
  -- things that should also trigger rebuilds
  -- ex. olean roots of dependencies
  moreDeps      : List FilePath
  buildParents  : List Name := []
  moreDepsMTime : IO.FS.SystemTime

structure BuildState where
  buildInfos : NameMap ModuleBuildInfo := ∅

abbrev BuildM := ReaderT BuildContext <| StateT BuildState IO

partial def buildModule (mod : Name) : BuildM ModuleBuildInfo := do
  let ctx ← read
  let pkg := ctx.package

  -- detect cyclic imports
  if ctx.buildParents.contains mod then
    let cycle := mod :: (ctx.buildParents.partition (· != mod)).1 ++ [mod]
    let cycle := cycle.map (s!"  {·}")
    throw <| IO.userError s!"import cycle detected:\n{"\n".intercalate cycle}"

  -- return previous result if already visited
  if let some info := (← get).buildInfos.find? mod then
    return info

  -- deduce lean file
  let leanFile := ctx.package.modToSource mod

  -- parse imports
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile leanFile) leanFile.toString
  let directLocalImports := imports.map (·.module) |>.filter (·.getRoot == pkg.module)

  -- recursively build local dependencies
  let depInfos ← directLocalImports.mapM fun i =>
    withReader (fun ctx => { ctx with buildParents := mod :: ctx.buildParents }) <|
      buildModule i

  -- calculate transitive `maxMTime`
  let leanMData ← leanFile.metadata
  let depMTimes ← depInfos.mapM (·.maxMTime)
  let maxMTime := List.maximum? (leanMData.modified :: ctx.moreDepsMTime :: depMTimes) |>.get!

  -- do build
  let cFile := pkg.modToC mod
  let oleanFile := pkg.modToOlean mod
  let info ← buildOleanAndC leanFile oleanFile cFile 
    depInfos maxMTime ctx.leanPath pkg.dir pkg.leanArgs
  modify fun st => { st with buildInfos := st.buildInfos.insert mod info }
  return info

def mkBuildContext (pkg : Package) (deps : List Package) : IO BuildContext := do
  let moreDeps := deps.map (·.oleanRoot)
  let moreDepsMTime := (← moreDeps.mapM (·.metadata)).map (·.modified) |>.maximum? |>.getD ⟨0, 0⟩
  let leanPath := SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  return { package := pkg, leanPath, moreDeps, moreDepsMTime }

def buildPackageModulesCore 
(pkg : Package) (deps : List Package) : IO (ModuleBuildInfo × BuildState) := do
  let crx ← mkBuildContext pkg deps
  buildModule pkg.module |>.run crx |>.run {}

def buildPackageModuleDAG 
(pkg : Package) (deps : List Package) : IO (NameMap ModuleBuildInfo) := do
  (← buildPackageModulesCore pkg deps).2.buildInfos

-- # Configure/Build Packages

def buildPackageModules 
(pkg : Package) (deps : List Package) : IO PUnit := do
  let (info, _) ← buildPackageModulesCore pkg deps
  if let Except.error _ ← IO.wait info.task then
    -- actual error has already been printed above
    throw <| IO.userError "Build failed."

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

def buildPackageOFiles (pkg : Package) (buildMap : NameMap ModuleBuildInfo)
: IO (List FilePath) := do 
  let oInfos ← buildMap.toList.mapM fun (mod, info) => 
    let oFile := pkg.modToO mod
    buildO oFile {info with artifact := info.cFile} pkg.leancArgs
  oInfos.mapM fun info => do
    IO.ofExcept (← IO.wait info.task)
    info.artifact

def buildStaticLib (pkg : Package) : IO FilePath := do
  let deps ← buildDeps pkg
  let buildMap ← buildPackageModuleDAG pkg deps
  let oFiles ← buildPackageOFiles pkg buildMap
  compileLib pkg.staticLibFile oFiles.toArray
  pkg.staticLibFile

def buildBin (pkg : Package) : IO FilePath := do
  let deps ← solveDeps pkg
  let depLibs ← deps.mapM buildStaticLib
  let buildMap ← buildPackageModuleDAG pkg deps
  let oFiles ← buildPackageOFiles pkg buildMap
  compileBin pkg.binFile (oFiles ++ depLibs).toArray pkg.linkArgs
  pkg.binFile

-- # Print Paths

def buildModulesInPackage (pkg : Package) (deps : List Package) (mods : List Name) : IO Unit := do
  let ctx ← mkBuildContext pkg deps
  let rs ← mods.mapM buildModule |>.run ctx |>.run' {}
  for r in rs do
    if let Except.error _ ← IO.wait r.task then
      -- actual error has already been printed above
      throw <| IO.userError "Build failed."

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

