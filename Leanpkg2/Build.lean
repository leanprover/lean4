/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Leanpkg2.Resolve
import Leanpkg2.Manifest
import Leanpkg2.BuildConfig
import Leanpkg2.Configure
import Leanpkg2.Make
import Leanpkg2.Proc

open Lean System

namespace Leanpkg2

structure BuildContext extends BuildConfig where
  parents       : List Name := []
  moreDepsMTime : IO.FS.SystemTime
  manifest      : Manifest

deriving instance Inhabited for IO.FS.SystemTime
deriving instance Inhabited for Task

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

  let srcPath := ctx.manifest.effectivePath
  let leanFile := modToFilePath srcPath mod "lean"
  let leanMData ← leanFile.metadata

  -- recursively build dependencies and calculate transitive `maxMTime`
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile leanFile) leanFile.toString
  let localImports := imports.filter (·.module.getRoot == ctx.pkg)
  let deps ← localImports.mapM (buildModule ·.module)
  let depMTimes ← deps.mapM (·.maxMTime)
  let maxMTime := List.maximum? (leanMData.modified :: ctx.moreDepsMTime :: depMTimes) |>.get!

  -- check whether we have an up-to-date .olean
  let oleanFile := modToFilePath (srcPath / buildPath) mod "olean"
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
      let cFile := modToFilePath (srcPath / tempBuildPath) mod "c"
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

def buildModules (manifest : Manifest) (cfg : BuildConfig) (mods : List Name) : IO Unit := do
  let moreDepsMTime := (← cfg.moreDeps.mapM (·.metadata)).map (·.modified) |>.maximum? |>.getD ⟨0, 0⟩
  let rs ← mods.mapM buildModule |>.run { toBuildConfig := cfg, moreDepsMTime, manifest } |>.run' {}
  for r in rs do
    if let Except.error _ ← IO.wait r.task then
      -- actual error has already been printed above
      throw <| IO.userError "Build failed."

def buildImports (manifest : Manifest) (cfg : Configuration) (imports leanArgs : List String := []) : IO Unit := do
  let imports := imports.map (·.toName)
  let root ← getRootPart <| manifest.effectivePath
  let localImports := imports.filter (·.getRoot == root)
  if localImports != [] then
    let buildCfg : BuildConfig := { pkg := root, leanArgs, leanPath := cfg.leanPath, moreDeps := cfg.moreDeps }
    if ← FilePath.pathExists "Makefile" then
      let oleans := localImports.map fun i =>
        Lean.modToFilePath (manifest.effectivePath / buildPath) i "olean" |>.toString
      execMake manifest oleans buildCfg
    else
      buildModules manifest buildCfg localImports

def printPaths (manifest : Manifest) (imports leanArgs : List String := []) : IO Unit := do
  let cfg ← configure manifest
  buildImports manifest cfg imports leanArgs
  IO.println cfg.leanPath
  IO.println cfg.leanSrcPath

def build (manifest : Manifest) (makeArgs leanArgs : List String := []) : IO Unit := do
  let cfg ← configure manifest
  let root ← getRootPart <| manifest.effectivePath
  let buildCfg : BuildConfig := { pkg := root, leanArgs, leanPath := cfg.leanPath, moreDeps := cfg.moreDeps }
  if makeArgs != [] || (← FilePath.pathExists "Makefile") then
    execMake manifest makeArgs buildCfg
  else
    buildModules manifest buildCfg [root]
