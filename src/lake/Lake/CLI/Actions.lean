/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Run
import Lake.Build.Targets
import Lake.Build.Common
import Lake.CLI.Build

namespace Lake
open Lean (Name)
open System (FilePath)

def env (cmd : String) (args : Array String := #[]) : LakeT IO UInt32 := do
  IO.Process.spawn {cmd, args, env := ← getAugmentedEnv} >>= (·.wait)

def exe (name : Name) (args  : Array String := #[]) (buildConfig : BuildConfig := {}) : LakeT IO UInt32 := do
  let ws ← getWorkspace
  let some exe := ws.findLeanExe? name
    | error s!"unknown executable `{name}`"
  let exeFile ← ws.runBuild exe.fetch buildConfig
  env exeFile.toString args

def Package.pack (pkg : Package) (file : FilePath := pkg.buildArchiveFile) : LogIO Unit := do
  logInfo s!"packing {file}"
  tar pkg.buildDir file

def Package.unpack (pkg : Package) (file : FilePath := pkg.buildArchiveFile) : LogIO Unit := do
  logInfo s!"unpacking {file}"
  untar file pkg.buildDir

def Package.uploadRelease (pkg : Package) (tag : String) : LogIO Unit := do
  pkg.pack
  logInfo s!"uploading {tag}:{pkg.buildArchive}"
  let mut args :=
    #["release", "upload", tag, pkg.buildArchiveFile.toString, "--clobber"]
  if let some repo := pkg.releaseRepo? then
    args := args.append #["-R", repo]
  proc {cmd := "gh", args}

def Package.resolveDriver
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

def Package.test (pkg : Package) (args : List String := []) (buildConfig : BuildConfig := {}) : LakeT IO UInt32 := do
  let cfgArgs := pkg.testDriverArgs
  let (pkg, driver) ← pkg.resolveDriver "test" pkg.testDriver
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

def Package.lint (pkg : Package) (args : List String := []) (buildConfig : BuildConfig := {}) : LakeT IO UInt32 := do
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
