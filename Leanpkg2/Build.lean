/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Leanpkg2.Resolve
import Leanpkg2.Package
import Leanpkg2.Make
import Leanpkg2.Proc

open Lean System

namespace Leanpkg2

structure BuildConfig where
  module   : Name
  leanArgs : List String
  leanPath : String
  -- things like `leanpkg.toml` and olean roots of dependencies that should also trigger rebuilds
  moreDeps : List FilePath

def mkBuildConfig
(pkg : Package) (deps : List Package) (leanArgs : List String)
: BuildConfig := {
  leanArgs,
  module := pkg.module
  leanPath := SearchPath.toString <| deps.map (·.buildDir)
  moreDeps := deps.filter (·.dir != pkg.dir) |>.map (·.oleanRoot)
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
        cmd := (← IO.appDir) / "lean" |>.withExtension FilePath.exeExtension |>.toString
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

def buildDeps (pkg : Package) : IO (List Package) := do
  let deps ← solveDeps pkg
  for dep in deps do
    unless dep.dir == pkg.dir do
      -- build recursively
      -- TODO: share build of common dependencies
      execCmd {
        cwd := dep.dir
        cmd := (← IO.appDir) / "lean" |>.toString
        args := #["--run", "Package.lean"]
      }
  return deps

def configure (pkg : Package) : IO Unit := do
  discard <| buildDeps pkg

def printPaths (pkg : Package) (imports leanArgs : List String := []) : IO Unit := do
  let deps ← buildDeps pkg
  buildImports pkg deps imports leanArgs
  IO.println <| SearchPath.toString <| deps.map (·.buildDir)
  IO.println <| SearchPath.toString <| deps.map (·.sourceDir)

def build (pkg : Package) (makeArgs leanArgs : List String := []) : IO Unit := do
  let deps ← buildDeps pkg
  if makeArgs != [] || (← FilePath.pathExists "Makefile") then
    execMake pkg deps makeArgs leanArgs
  else
    buildModules (mkBuildConfig pkg deps leanArgs) [pkg.module]
