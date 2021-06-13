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
  leanPath := SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  moreDeps := deps.map (·.oleanRoot)
}

structure BuildContext extends BuildConfig where
  parents       : List Name := []
  moreDepsMTime : IO.FS.SystemTime

structure BuildResult where
  maxMTime : IO.FS.SystemTime
  task     : Task (Except IO.Error Unit)
  deriving Inhabited

structure BuildState where
  modTasks : NameMap BuildResult := ∅

abbrev BuildM := ReaderT BuildContext <| StateT BuildState IO

partial def buildModule (mod : Name) : BuildM BuildResult := do
  let ctx ← read

  -- detect cyclic imports
  if ctx.parents.contains mod then
    let cycle := mod :: (ctx.parents.partition (· != mod)).1 ++ [mod]
    let cycle := cycle.map (s!"  {·}")
    throw <| IO.userError s!"import cycle detected:\n{"\n".intercalate cycle}"

  -- skip if already visited
  if let some res := (← get).modTasks.find? mod then
    return res

  -- deduce lean file
  let leanFile := modToFilePath "." mod "lean"

  -- parse imports
  let (imports, _, _) ← Elab.parseImports (← IO.FS.readFile leanFile) leanFile.toString
  let localImports := imports.filter (·.module.getRoot == ctx.module)

  -- recursively build local dependencies
  let deps ← localImports.mapM fun i =>
    withReader (fun ctx => { ctx with parents := mod :: ctx.parents }) <|
      buildModule i.module

  -- calculate transitive `maxMTime`
  let leanMData ← leanFile.metadata
  let depMTimes ← deps.mapM (·.maxMTime)
  let maxMTime := List.maximum? (leanMData.modified :: ctx.moreDepsMTime :: depMTimes) |>.get!

  -- check whether we have an up-to-date .olean
  let oleanFile := modToFilePath buildPath mod "olean"
  try
    if (← oleanFile.metadata).modified >= maxMTime then
      let res := { maxMTime, task := Task.pure (Except.ok ()) }
      modify fun st => { st with modTasks := st.modTasks.insert mod res }
      return res
  catch
    | IO.Error.noFileOrDirectory .. => pure ()
    | e                             => throw e

  -- (try to) compile the olean and c file
  let task ← IO.mapTasks (tasks := deps.map (·.task)) fun rs => do
    if let some e := rs.findSome? (fun | Except.error e => some e | Except.ok _ => none) then
      -- propagate failure from dependencies
      throw e
    try
      let cFile := modToFilePath tempBuildPath mod "c"
      IO.FS.createDirAll oleanFile.parent.get!
      IO.FS.createDirAll cFile.parent.get!
      execCmd {
        cmd := "lean"
        args := ctx.leanArgs.toArray ++ #["-o", oleanFile.toString, "-c", cFile.toString, leanFile.toString]
        env := #[("LEAN_PATH", ctx.leanPath)]
      }
    catch e =>
      -- print compile errors early
      IO.eprintln e
      throw e

  let res := { maxMTime, task := task }
  modify fun st => { st with modTasks := st.modTasks.insert mod res }
  return res

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
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.sourceDir :: deps.map (·.sourceDir)

private def relPathToUnixString (path : FilePath) : String :=
  if Platform.isWindows then
    path.toString.map fun c => if c == '\\' then '/' else c
  else
    path.toString

def build (pkg : Package) (makeArgs leanArgs : List String := []) : IO Unit := do
  if makeArgs.contains "bin" then
    let deps ← buildDeps pkg ["lib"]
    let depLibs := SearchPath.toString <| deps.map (relPathToUnixString ·.staticLibPath)
    buildPkg pkg deps (s!"LINK_OPTS=\"{depLibs}\"" :: makeArgs) leanArgs
  else
    let deps ← buildDeps pkg
    buildPkg pkg deps makeArgs leanArgs
