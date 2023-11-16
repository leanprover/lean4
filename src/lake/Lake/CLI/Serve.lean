/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load
import Lake.Build
import Lake.Util.MainM
import Lean.Util.FileSetupInfo

namespace Lake
open Lean

/-- Exit code to return if `setup-file` cannot find the config file. -/
def noConfigFileCode : ExitCode := 2

/--
Environment variable that is set when `lake serve` cannot parse the Lake configuration file
and falls back to plain `lean --server`.
-/
def invalidConfigEnvVar := "LAKE_INVALID_CONFIG"

/--
Build a list of imports of a file and print the `.olean` and source directories of every used package, as well as the server options for the file.
If no configuration file exists, exit silently with `noConfigFileCode` (i.e, 2).

The `setup-file` command is used internally by Lean 4 server.
-/
def setupFile (loadConfig : LoadConfig) (path : FilePath) (imports : List String := [])
(buildConfig : BuildConfig := {}) (verbosity : Verbosity := .normal) : MainM PUnit := do
  if (← loadConfig.configFile.pathExists) then
    if let some errLog := (← IO.getEnv invalidConfigEnvVar) then
      IO.eprint errLog
      IO.eprintln s!"Invalid Lake configuration.  Please restart the server after fixing the Lake configuration file."
      exit 1
    let ws ← MainM.runLogIO (loadWorkspace loadConfig) verbosity
    let dynlibs ← ws.runBuild (buildImportsAndDeps imports) buildConfig
      |>.run (MonadLog.eio verbosity)
    let paths : LeanPaths := {
      oleanPath := ws.leanPath
      srcPath := ws.leanSrcPath
      loadDynlibPaths := dynlibs
      : LeanPaths
    }
    let setupOptions : LeanOptions ← do
      let some moduleName ← searchModuleNameOfFileName path ws.leanSrcPath
        | pure ⟨∅⟩
      let some module := ws.findModule? moduleName
        | pure ⟨∅⟩
      let options := module.serverOptions.map fun opt => ⟨opt.name, opt.value⟩
      pure ⟨Lean.RBMap.fromArray options Lean.Name.cmp⟩
    IO.println <| Json.compress <| toJson {
      paths,
      setupOptions
      : FileSetupInfo
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
      pure (← LakeT.run ctx getAugmentedEnv, ws.root.moreGlobalServerArgs)
    else
      IO.eprintln "warning: package configuration has errors, falling back to plain `lean --server`"
      pure (config.env.baseVars.push (invalidConfigEnvVar, log), #[])
  (← IO.Process.spawn {
    cmd := config.env.lean.lean.toString
    args := #["--server"] ++ moreServerArgs ++ args
    env := extraEnv
  }).wait
