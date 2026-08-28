/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Load.Config
public import Lake.Build.Context
public import Lake.Util.Exit
import Lake.Build.Run
import Lake.Build.Module
import Lake.Load.Package
import Lake.Load.Lean.Elab
import Lake.Load.Workspace
import Lake.Util.IO

open Lean
open System (FilePath)

namespace Lake

/-- Exit code to return if `setup-file` cannot find the config file. -/
public def noConfigFileCode : ExitCode := 2

/--
Environment variable that is set when `lake serve` cannot parse the Lake configuration file
and falls back to plain `lean --server`.
-/
public def invalidConfigEnvVar := "LAKE_INVALID_CONFIG"

/--
Build the dependencies of a Lean file and print the computed module's setup as JSON.
If `header?` is not `none`, it will be used to determine imports instead of the
file's own header.

Requires a configuration file to succeed. If no configuration file exists, it
will exit silently with `noConfigFileCode` (i.e, 2).

The `setup-file` command is used internally by the Lean server.
-/
public def setupFile
  (loadConfig : LoadConfig) (leanFile : FilePath)
  (header? : Option ModuleHeader := none) (buildConfig : BuildConfig := {})
: BaseIO ExitCode := do
  let path ← resolvePath leanFile
  let configFile ← realConfigFile loadConfig.configFile
  if configFile.toString.isEmpty then
    return noConfigFileCode
  else if configFile == path then do
    let setup : ModuleSetup := {
      name := configModuleName
      plugins :=  #[loadConfig.lakeEnv.lake.sharedLib]
    }
    print! (toJson setup).compress
  else if let some errLog := (← IO.getEnv invalidConfigEnvVar) then
    eprint! errLog
    eprint! "Failed to configure the Lake workspace. \
      Please restart the server after fixing the error above.\n"
    return 1
  else
    let some ws ← loadWorkspace loadConfig |>.toBaseIO buildConfig.toLogConfig
      | eprint! "Failed to load the Lake workspace.\n"
        return 1
    let setup := ws.runBuild (cfg := buildConfig) do
      setupServerModule leanFile.toString path header?
    match (← setup.toBaseIO) with
    | .ok setup =>
      print! (toJson setup).compress
    | .error _ =>
      eprint! "Failed to build module dependencies.\n"
      return 1
where
  print! msg := do
    match (← IO.println msg |>.toBaseIO) with
    | .ok _ =>
      return 0
    | .error e =>
      panic! s!"Failed to print `setup-file` result: {e}"
      return 1
  eprint! msg := do
    IO.eprint msg |>.catchExceptions fun e =>
      panic! s!"Failed to print `setup-file` error: {e}\nOriginal error:\n{msg}"

/--
Start the Lean LSP for the `Workspace` loaded from `config`
with the given additional `args`.
-/
public def serve (config : LoadConfig) (args : Array String) : IO UInt32 := do
  let (extraEnv, moreServerArgs) ← do
    let (ws?, log) ← (loadWorkspace config).captureLog
    log.replay (logger := MonadLog.stderr)
    if let some ws := ws? then
      pure (ws.augmentedEnvVars, ws.root.moreGlobalServerArgs)
    else
      IO.eprintln "warning: package configuration has errors, falling back to plain `lean --server`"
      pure (config.lakeEnv.baseVars.push (invalidConfigEnvVar, log.toString), #[])
  (← IO.Process.spawn {
    cmd := config.lakeEnv.lean.lean.toString
    args := #["--server"] ++ moreServerArgs ++ args
    env := extraEnv
  }).wait
