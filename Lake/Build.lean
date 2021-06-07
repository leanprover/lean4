/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Resolve
import Lake.Package
import Lake.Make
import Lake.Proc

open Lean System

namespace Lake

structure BuildConfig where
  module   : Name
  leanArgs : List String
  leanPath : String
  -- things that should also trigger rebuilds
  -- ex. olean roots of dependencies
  moreDeps : List FilePath

def mkBuildConfig
(pkg : Package) (deps : List Package) (leanArgs : List String)
: BuildConfig := {
  leanArgs,
  module := pkg.module
  leanPath := SearchPath.toString <| pkg.buildDir :: deps.map (·.buildDir)
  moreDeps := deps.map (·.oleanRoot)
}

structure BuildContext extends BuildConfig where
  parents       : List Name := []
  moreDepsMTime : IO.FS.SystemTime

structure Result where
  maxMTime : IO.FS.SystemTime
  task     : Task (Except IO.Error Unit)
  deriving Inhabited

structure State where
  modTasks : NameMap Result := ∅

abbrev BuildM := ReaderT BuildContext <| StateT State IO

partial def buildModule (mod : Name) : BuildM Result := do
  let ctx ← read
  if ctx.parents.contains mod then
    -- cyclic import
    let cycle := ctx.parents.dropWhile (· != mod) ++ [mod]
    let cycle := cycle.reverse.map (s!"  {·}")
    throw <| IO.userError s!"import cycle detected:\n{"\n".intercalate cycle}"

  if let some r := (← get).modTasks.find? mod then
    -- already visited
    return r

  let leanFile := modToFilePath "." mod "lean"
  let leanMData ← leanFile.metadata

  -- recursively build dependencies and calculate transitive `maxMTime`
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile leanFile) leanFile.toString
  let localImports := imports.filter (·.module.getRoot == ctx.module)
  let deps ← localImports.mapM (buildModule ·.module)
  let depMTimes ← deps.mapM (·.maxMTime)
  let maxMTime := List.maximum? (leanMData.modified :: ctx.moreDepsMTime :: depMTimes) |>.get!

  -- check whether we have an up-to-date .olean
  let oleanFile := modToFilePath buildPath mod "olean"
  try
    if (← oleanFile.metadata).modified >= maxMTime then
      let r := { maxMTime, task := Task.pure (Except.ok ()) }
      modify fun st => { st with modTasks := st.modTasks.insert mod r }
      return r
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e                             => throw e

  let task ← IO.mapTasks (tasks := deps.map (·.task)) fun rs => do
    if let some e := rs.findSome? (fun | Except.error e => some e | Except.ok _ => none) then
      -- propagate failure
      throw e
    try
      let cFile := modToFilePath tempBuildPath mod "c"
      IO.createDirAll oleanFile.parent.get!
      IO.createDirAll cFile.parent.get!
      execCmd {
        cmd := FilePath.withExtension "lean" FilePath.exeExtension |>.toString
        args := ctx.leanArgs.toArray ++ #["-o", oleanFile.toString, "-c", cFile.toString, leanFile.toString]
        env := #[("LEAN_PATH", ctx.leanPath)]
      }
    catch e =>
      -- print errors early
      IO.eprintln e
      throw e

  let r := { maxMTime, task := task }
  modify fun st => { st with modTasks := st.modTasks.insert mod r }
  return r

def buildModules (cfg : BuildConfig) (mods : List Name) : IO Unit := do
  let moreDepsMTime := (← cfg.moreDeps.mapM (·.metadata)).map (·.modified) |>.maximum? |>.getD ⟨0, 0⟩
  let rs ← mods.mapM buildModule |>.run { toBuildConfig := cfg, moreDepsMTime } |>.run' {}
  for r in rs do
    if let Except.error _ ← IO.wait r.task then
      -- actual error has already been printed above
      throw <| IO.userError "Build failed."

def buildImports (pkg : Package) (deps : List Package) (imports leanArgs : List String := []) : IO Unit := do
  let imports := imports.map (·.toName)
  let localImports := imports.filter (·.getRoot == pkg.module)
  if localImports != [] then
    if ← FilePath.pathExists "Makefile" then
      let oleans := localImports.map fun i =>
        Lean.modToFilePath buildPath i "olean" |>.toString
      execMake pkg deps oleans leanArgs
    else
      buildModules (mkBuildConfig pkg deps leanArgs) localImports

def buildPkg (pkg : Package) (deps : List Package) (makeArgs leanArgs : List String := []) : IO Unit := do
  if makeArgs != [] || (← FilePath.pathExists "Makefile") then
    execMake pkg deps makeArgs leanArgs
  else
    buildModules (mkBuildConfig pkg deps leanArgs) [pkg.module]

def buildDeps (pkg : Package) (makeArgs leanArgs : List String := []) : IO (List Package) := do
  let deps ← solveDeps pkg
  for dep in deps do
    -- build recursively
    -- TODO: share build of common dependencies
    let depDeps ← solveDeps dep
    buildPkg dep depDeps makeArgs leanArgs
  return deps

def configure (pkg : Package) : IO Unit :=
  discard <| buildDeps pkg

def printPaths (pkg : Package) (imports leanArgs : List String := []) : IO Unit := do
  let deps ← buildDeps pkg
  buildImports pkg deps imports leanArgs
  IO.println <| SearchPath.toString <| pkg.buildDir :: deps.map (·.buildDir)
  IO.println <| SearchPath.toString <| pkg.sourceDir :: deps.map (·.sourceDir)

def build (pkg : Package) (makeArgs leanArgs : List String := []) : IO Unit := do
  let deps ← buildDeps pkg (if makeArgs.contains "bin" then ["lib"] else [])
  buildPkg pkg deps makeArgs leanArgs
