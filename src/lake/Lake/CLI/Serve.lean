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
def printPaths (loadConfig : LoadConfig) (imports : List String := [])
(buildConfig : BuildConfig := {}) (verbosity : Verbosity := .normal) : MainM PUnit := do
  if (← loadConfig.configFile.pathExists) then
    if let some errLog := (← IO.getEnv invalidConfigEnvVar) then
      IO.eprint errLog
      IO.eprintln s!"Invalid Lake configuration.  Please restart the server after fixing the Lake configuration file."
      exit 1
    let ws ← MainM.runLogIO (loadWorkspace loadConfig) verbosity
    let dynlibs ← ws.runBuild (buildImportsAndDeps imports) buildConfig
      |>.run (MonadLog.eio verbosity)
    IO.println <| Json.compress <| toJson {
      oleanPath := ws.leanPath
      srcPath := ws.leanSrcPath
      loadDynlibPaths := dynlibs
      : LeanPaths
    }
  else
    exit noConfigFileCode

/--
Start the Lean LSP for the `Workspace` loaded from `config`
with the given additional `args`.
-/
def serve (config : LoadConfig) (args : Array String) : IO UInt32 := do
  let (extraEnv, moreServerArgs) ← do
    let (log, ws?) ← loadWorkspace config |>.captureLog
    IO.eprint log
    if let some ws := ws? then
      let ctx := mkLakeContext ws
      pure (← LakeT.run ctx getAugmentedEnv, ws.root.moreServerArgs)
    else
      IO.eprintln "warning: package configuration has errors, falling back to plain `lean --server`"
      pure (config.env.baseVars.push (invalidConfigEnvVar, log), #[])
  (← IO.Process.spawn {
    cmd := config.env.lean.lean.toString
    args := #["--server"] ++ moreServerArgs ++ args
    env := extraEnv
  }).wait
