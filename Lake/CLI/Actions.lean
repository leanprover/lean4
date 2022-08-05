/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load
import Lake.Build
import Lake.Util.MainM

namespace Lake
open Lean (Json toJson fromJson? LeanPaths)

/-- Exit code to return if `print-paths` cannot find the config file. -/
def noConfigFileCode : ExitCode := 2

/--
Environment variable that is set when `lake serve` cannot parse the Lake configuration file
and falls back to plain `lean --server`.
-/
def invalidConfigEnvVar := "LAKE_INVALID_CONFIG"

/--
Build a list of imports of the package
and print the `.olean` and source directories of every used package.
If no configuration file exists, exit silently with `noConfigFileCode` (i.e, 2).

The `print-paths` command is used internally by Lean 4 server.
-/
def printPaths (config : LoadConfig) (imports : List String := []) (oldMode : Bool := false) : MainM PUnit := do
  let configFile := config.rootDir / config.configFile
  if (← configFile.pathExists) then
    if (← IO.getEnv invalidConfigEnvVar) matches some .. then
      IO.eprintln s!"Error parsing '{configFile}'.  Please restart the lean server after fixing the Lake configuration file."
      exit 1
    let ws ← MainM.runLogIO (loadWorkspace config) config.verbosity
    let dynlibs ← ws.runBuild (buildImportsAndDeps imports) oldMode
      |>.run (MonadLog.eio config.verbosity)
    IO.println <| Json.compress <| toJson {
      oleanPath := ws.leanPath
      srcPath := ws.leanSrcPath
      loadDynlibPaths := dynlibs
      : LeanPaths
    }
  else
    exit noConfigFileCode

def serve (config : LoadConfig) (args : Array String) : LogIO UInt32 := do
  let (extraEnv, moreServerArgs) ←
    try
      let ws ← loadWorkspace config
      let ctx := mkLakeContext ws
      pure (← LakeT.run ctx getAugmentedEnv, ws.root.moreServerArgs)
    else
      logWarning "package configuration has errors, falling back to plain `lean --server`"
      pure (config.env.installVars.push (invalidConfigEnvVar, "1"), #[])
  (← IO.Process.spawn {
    cmd := config.env.lean.lean.toString
    args := #["--server"] ++ moreServerArgs ++ args
    env := extraEnv
  }).wait

def env (cmd : String) (args : Array String := #[]) : LakeT IO UInt32 := do
  IO.Process.spawn {cmd, args, env := ← getAugmentedEnv} >>= (·.wait)

def exe (name : Name) (args  : Array String := #[]) (oldMode := false) : LakeT LogIO UInt32 := do
  let ws ← getWorkspace
  if let some exe := ws.findLeanExe? name then
    let exeFile ← ws.runBuild (exe.build >>= (·.await)) oldMode
    env exeFile.toString args
  else
    error s!"unknown executable `{name}`"

def uploadRelease (pkg : Package) (tag : String) : LogIO Unit := do
  let mut args :=
    #["release", "upload", tag, pkg.buildArchiveFile.toString, "--clobber"]
  if let some repo := pkg.releaseRepo? then
    args := args.append #["-R", repo]
  tar pkg.buildArchive pkg.buildDir pkg.buildArchiveFile
    (excludePaths := #["*.tar.gz", "*.tar.gz.trace"])
  logInfo s!"Uploading {tag}/{pkg.buildArchive}"
  proc {cmd := "gh", args}
