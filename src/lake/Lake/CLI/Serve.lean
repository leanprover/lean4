/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Load
import Lake.Build
import Lake.Util.MainM
import Lean.Util.FileSetupInfo

open Lean
open System (FilePath)

namespace Lake

/-- Exit code to return if `setup-file` cannot find the config file. -/
def noConfigFileCode : ExitCode := 2

/--
Environment variable that is set when `lake serve` cannot parse the Lake configuration file
and falls back to plain `lean --server`.
-/
def invalidConfigEnvVar := "LAKE_INVALID_CONFIG"

private def mkLeanPaths (ws : Workspace) (deps : ModuleDeps) : LeanPaths where
  oleanPath := ws.leanPath
  srcPath := ws.leanSrcPath
  loadDynlibPaths := deps.dynlibs.map (·.path)
  pluginPaths := deps.plugins.map (·.path)

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
  let path ← resolvePath path
  let configFile ← realConfigFile loadConfig.configFile
  if configFile.toString.isEmpty then
    exit noConfigFileCode
  else if configFile == path then do
    let info : FileSetupInfo := {
      paths := {
        oleanPath := loadConfig.lakeEnv.leanPath
        srcPath := loadConfig.lakeEnv.leanSrcPath
        pluginPaths := #[loadConfig.lakeEnv.lake.sharedLib]
      }
      setupOptions := ⟨∅⟩
    }
    IO.println (toJson info).compress
  else if let some errLog := (← IO.getEnv invalidConfigEnvVar) then
    IO.eprint errLog
    IO.eprintln s!"Failed to configure the Lake workspace. Please restart the server after fixing the error above."
    exit 1
  else
    let some ws ← loadWorkspace loadConfig |>.toBaseIO buildConfig.outLv buildConfig.ansiMode
      | error "failed to load workspace"
    if let some mod := ws.findModuleBySrc? path then
      let deps ← ws.runBuild (withRegisterJob s!"setup ({mod.name})" do mod.deps.fetch) buildConfig
      let info : FileSetupInfo := {
        paths := mkLeanPaths ws deps
        setupOptions := mod.serverOptions
      }
      IO.println (toJson info).compress
    else
      let imports := imports.foldl (init := #[]) fun imps imp =>
        if let some mod := ws.findModule? imp.toName then imps.push mod else imps
      let deps ← ws.runBuild (buildImportsAndDeps path imports) buildConfig
      let info : FileSetupInfo := {
        paths := mkLeanPaths ws deps
        setupOptions := ⟨∅⟩
      }
      IO.println (toJson info).compress

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
