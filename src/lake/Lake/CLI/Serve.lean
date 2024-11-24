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
open System (FilePath)

/-- Exit code to return if `setup-file` cannot find the config file. -/
def noConfigFileCode : ExitCode := 2

/--
Environment variable that is set when `lake serve` cannot parse the Lake configuration file
and falls back to plain `lean --server`.
-/
def invalidConfigEnvVar := "LAKE_INVALID_CONFIG"

/--
Build a list of imports of a file and print the `.olean` and source directories
of every used package, as well as the server options for the file.
If no configuration file exists, exit silently with `noConfigFileCode` (i.e, 2).

The `setup-file` command is used internally by the Lean 4 server.
-/
def setupFile
  (loadConfig : LoadConfig) (path : FilePath) (imports : List String := [])
  (buildConfig : BuildConfig := {})
: MainM PUnit := do
  if (← configFileExists loadConfig.configFile) then
    if let some errLog := (← IO.getEnv invalidConfigEnvVar) then
      IO.eprint errLog
      IO.eprintln s!"Invalid Lake configuration.  Please restart the server after fixing the Lake configuration file."
      exit 1
    let outLv := buildConfig.verbosity.minLogLv
    let ws ← MainM.runLoggerIO (minLv := outLv) (ansiMode := .noAnsi) do
      loadWorkspace loadConfig
    let imports := imports.foldl (init := #[]) fun imps imp =>
      if let some mod := ws.findModule? imp.toName then imps.push mod else imps
    let dynlibs ← MainM.runLogIO (minLv := outLv) (ansiMode := .noAnsi) do
      ws.runBuild (buildImportsAndDeps path imports) buildConfig
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
    let (ws?, log) ← (loadWorkspace config).captureLog
    log.replay (logger := MonadLog.stderr)
    if let some ws := ws? then
      let ctx := mkLakeContext ws
      pure (← LakeT.run ctx getAugmentedEnv, ws.root.moreGlobalServerArgs)
    else
      IO.eprintln "warning: package configuration has errors, falling back to plain `lean --server`"
      pure (config.lakeEnv.baseVars.push (invalidConfigEnvVar, log.toString), #[])
  (← IO.Process.spawn {
    cmd := config.lakeEnv.lean.lean.toString
    args := #["--server"] ++ moreServerArgs ++ args
    env := extraEnv
  }).wait
