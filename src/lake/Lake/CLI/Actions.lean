/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Workspace
import Lake.Build.Run
import Lake.Build.Actions
import Lake.Build.Targets
import Lake.Build.Module
import Lake.CLI.Build
import Lake.Util.Proc

namespace Lake
open Lean (Name)
open System (FilePath)

public def env (cmd : String) (args : Array String := #[]) : LakeT IO UInt32 := do
  IO.Process.spawn {cmd, args, env := ← getAugmentedEnv} >>= (·.wait)

public def exe
  (name : Name) (args  : Array String := #[]) (buildConfig : BuildConfig := {})
: LakeT IO UInt32 := do
  let ws ← getWorkspace
  let some exe := ws.findLeanExe? name
    | error s!"unknown executable `{name}`"
  let exeFile ← ws.runBuild exe.fetch buildConfig
  env exeFile.toString args

public def Package.pack
  (pkg : Package) (file : FilePath := pkg.buildArchiveFile)
: LogIO Unit := do
  logInfo s!"packing {file}"
  tar pkg.buildDir file

public def Package.unpack
  (pkg : Package) (file : FilePath := pkg.buildArchiveFile)
: LogIO Unit := do
  logInfo s!"unpacking {file}"
  untar file pkg.buildDir

public def Package.uploadRelease
  (pkg : Package) (tag : String)
: LogIO Unit := do
  pkg.pack
  logInfo s!"uploading {tag}:{pkg.buildArchive}"
  let mut args :=
    #["release", "upload", tag, pkg.buildArchiveFile.toString, "--clobber"]
  if let some repo := pkg.releaseRepo? then
    args := args.append #["-R", repo]
  proc {cmd := "gh", args}

public def Package.resolveDriver
  (pkg : Package) (kind : String) (driver : String)
: LakeT IO (Package × String) := do
  let pkgName := pkg.name.toString (escape := false)
  if driver.isEmpty then
    error s!"{pkgName}: no {kind} driver configured"
  else
    match driver.split (· == '/') with
    | [pkg, driver] =>
      let some pkg ← findPackage? pkg.toName
        | error s!"{pkgName}: unknown {kind} driver package '{pkg}'"
      return (pkg, driver)
    | [driver] =>
      return (pkg, driver)
    | _ =>
      error s!"{pkgName}: invalid {kind} driver '{driver}' (too many '/')"

public def Package.runSingleTestDriver
  (pkg : Package) (driverName : String) (cfgArgs : Array String)
  (args : List String) (buildConfig : BuildConfig)
: LakeT IO UInt32 := do
  let (pkg, driver) ← pkg.resolveDriver "test" driverName
  let pkgName := pkg.name.toString (escape := false)
  if let some script := pkg.scripts.find? driver.toName then
    script.run (cfgArgs.toList ++ args)
  else if let some exe := pkg.findLeanExe? driver.toName  then
    let exeFile ← runBuild exe.fetch buildConfig
    env exeFile.toString (cfgArgs ++ args.toArray)
  else if let some lib := pkg.findLeanLib? driver.toName then
    unless cfgArgs.isEmpty ∧ args.isEmpty do
      error s!"{pkgName}: arguments cannot be passed to a library test driver"
    match resolveLibTarget (← getWorkspace) lib with
    | .ok specs =>
      runBuild (buildSpecs specs) {buildConfig with out := .stdout}
      return 0
    | .error e =>
      error s!"{pkgName}: invalid test driver: {e}"
  else
    error s!"{pkgName}: invalid test driver: unknown script, executable, or library '{driver}'"

public def Package.test
  (pkg : Package) (args : List String := []) (buildConfig : BuildConfig := {})
: LakeT IO UInt32 := do
  let cfgArgs := pkg.testDriverArgs
  let pkgName := pkg.name.toString (escape := false)

  -- Collect all drivers to run
  let mut allDrivers : Array String := #[]

  -- Add primary testDriver if specified
  if !pkg.testDriver.isEmpty then
    allDrivers := allDrivers.push pkg.testDriver

  -- Add all testDrivers
  allDrivers := allDrivers ++ pkg.testDrivers

  -- Check if we have any drivers
  if allDrivers.isEmpty then
    error s!"{pkgName}: no test driver configured"

  -- Run each driver in sequence, propagating first non-zero exit code
  let mut lastExitCode : UInt32 := 0
  for driver in allDrivers do
    let exitCode ← pkg.runSingleTestDriver driver cfgArgs args buildConfig
    if exitCode != 0 then
      return exitCode
    lastExitCode := exitCode

  return lastExitCode

public def Package.lint
  (pkg : Package) (args : List String := []) (buildConfig : BuildConfig := {})
: LakeT IO UInt32 := do
  let cfgArgs := pkg.lintDriverArgs
  let (pkg, driver) ← pkg.resolveDriver "lint" pkg.lintDriver
  if let some script := pkg.scripts.find? driver.toName then
    script.run (cfgArgs.toList ++ args)
  else if let some exe := pkg.findLeanExe? driver.toName  then
    let exeFile ← runBuild exe.fetch buildConfig
    env exeFile.toString (cfgArgs ++ args.toArray)
  else
    let pkgName := pkg.name.toString (escape := false)
    error s!"{pkgName}: invalid lint driver: unknown script or executable '{driver}'"

/--
Run `lean` on file using configuration from the workspace.

Additional arguments can be passed to `lean` via `moreArgs` and the
building of dependencies can be further configured via `buildConfig`.
-/
public def Workspace.evalLeanFile
  (ws : Workspace) (leanFile : FilePath)
  (moreArgs : Array String := #[]) (buildConfig : BuildConfig := {})
: IO UInt32 := do
  let spawnArgs ← ws.runBuild (cfg := buildConfig) do
    prepareLeanCommand leanFile moreArgs
  let child ← IO.Process.spawn spawnArgs
  child.wait
