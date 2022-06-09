/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

import Lake.Config.Load
import Lake.Config.SearchPath
import Lake.Config.InstallPath
import Lake.Config.Manifest
import Lake.Config.Resolve
import Lake.Util.Error
import Lake.Util.MainM
import Lake.Util.Cli
import Lake.CLI.Init
import Lake.CLI.Help
import Lake.CLI.Build
import Lake.CLI.Error

open System
open Lean (Name Json toJson fromJson?)

namespace Lake

def Package.clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir

-- # Loading Lake Config

structure LakeConfig where
  rootDir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  leanInstall : LeanInstall
  lakeInstall : LakeInstall
  args : List String := []

def loadPkg (config : LakeConfig) : LogT IO Package := do
  setupLeanSearchPath config.leanInstall config.lakeInstall
  Package.load config.rootDir config.args (config.rootDir / config.configFile)

def loadManifestMap (manifestFile : FilePath) : LogT IO (Lean.NameMap PackageEntry) := do
  if let Except.ok contents ← IO.FS.readFile manifestFile  |>.toBaseIO then
    match Json.parse contents with
      | Except.ok json =>
        match fromJson? json with
        | Except.ok (manifest : Manifest) =>
          pure manifest.toMap
        | Except.error e =>
          logWarning s!"improperly formatted package manifest: {e}"
          pure {}
      | Except.error e =>
        logWarning s!"invalid JSON in package manifest: {e}"
        pure {}
  else
    pure {}

def loadWorkspace (config : LakeConfig) (updateDeps := false) : LogT IO Workspace := do
  let pkg ← loadPkg config
  let ws := Workspace.ofPackage pkg
  let manifestMap ← loadManifestMap ws.manifestFile
  let (packageMap, resolvedMap) ← resolveDeps ws pkg updateDeps |>.run manifestMap
  unless resolvedMap.isEmpty do
    IO.FS.writeFile ws.manifestFile <| Json.pretty <| toJson <| Manifest.fromMap resolvedMap
  let packageMap := packageMap.insert pkg.name pkg
  return {ws with packageMap}

-- # CLI

structure LakeOptions where
  rootDir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  leanInstall? : Option LeanInstall := none
  lakeInstall? : Option LakeInstall := none
  subArgs : List String := []
  wantsHelp : Bool := false

abbrev CliMainM := ExceptT CliError MainM
abbrev CliStateM := StateT LakeOptions CliMainM
abbrev CliM := ArgsT CliStateM

namespace Cli

-- ## Option Management

def getWantsHelp : CliStateM Bool :=
  (·.wantsHelp) <$> get

def setLean (lean : String) : CliStateM PUnit := do
  let leanInstall? ← findLeanCmdInstall? lean
  modify ({·  with leanInstall?})

-- ## Other Option Helpers

/-- Get the Lean installation. Error if missing. -/
def getLeanInstall (opts : LakeOptions) : Except CliError LeanInstall := do
  if let some leanInstall := opts.leanInstall? then
    return leanInstall
  else
    throw CliError.unknownLeanInstall

/-- Get the Lake installation. Error if missing. -/
def getLakeInstall (opts : LakeOptions) : Except CliError LakeInstall := do
  if let some lakeInstall := opts.lakeInstall? then
    return lakeInstall
  else
    throw CliError.unknownLakeInstall

/-- Get the Lean and Lake installation. Error if either is missing. -/
def getInstall (opts : LakeOptions) : Except CliError (LeanInstall × LakeInstall) := do
  return (← getLeanInstall opts, ← getLakeInstall opts)

/-- Make a `LakeConfig` from a `LakeOptions`. -/
def mkLakeConfig (opts : LakeOptions) (args : List String := []) : Except CliError LakeConfig := do
  let (leanInstall, lakeInstall) ← getInstall opts
  return {
    rootDir := opts.rootDir,
    configFile := opts.configFile,
    leanInstall, lakeInstall, args
  }

/-- Load configuration using CLI state and run the `LakeT` action. -/
def runLakeT [MonadLiftT m CliStateM] (x : LakeT m α) : CliStateM α := do
  let config ← mkLakeConfig (← get)
  let ws ← loadWorkspace config
  liftM <| x.run {
    lean := config.leanInstall,
    lake := config.lakeInstall,
    opaqueWs := ws
  }

-- ## Argument Parsing

def takeArg (arg : String) : CliM String := do
  match (← takeArg?) with
  | none => throw <| CliError.missingArg arg
  | some arg => pure arg

def takeOptArg (opt arg : String) : CliM String := do
  match (← takeArg?) with
  | none => throw <| CliError.missingOptArg opt arg
  | some arg => pure arg

/--
Verify that there are no CLI arguments remaining
before running the given action.
-/
def noArgsRem (act : CliStateM α) : CliM α := do
  let args ← getArgs
  if args.isEmpty then act else
    throw <| CliError.unexpectedArguments args

-- ## Option Parsing

def shortOption : (opt : Char) → CliM PUnit
| 'h' => modifyThe LakeOptions ({· with wantsHelp := true})
| 'd' => do let rootDir ← takeOptArg "-d" "path"; modifyThe LakeOptions ({· with rootDir})
| 'f' => do let configFile ← takeOptArg "-f" "path"; modifyThe LakeOptions ({· with configFile})
| opt => throw <| CliError.unknownShortOption opt

def longOption : (opt : String) → CliM PUnit
| "--help"  => modifyThe LakeOptions ({· with wantsHelp := true})
| "--dir"   => do let rootDir ← takeOptArg "--dir" "path"; modifyThe LakeOptions ({· with rootDir})
| "--file"  => do let configFile ← takeOptArg "--file" "path"; modifyThe LakeOptions ({· with configFile})
| "--lean"  => do setLean <| ← takeOptArg "--lean" "path or command"
| "--"      => do let subArgs ← takeArgs; modifyThe LakeOptions ({· with subArgs})
| opt       => throw <| CliError.unknownLongOption opt

def lakeOption :=
  option {
    short := shortOption
    long := longOption
    longShort := shortOptionWithArg shortOption
  }

-- ## Commands

/-- Verify the Lean version Lake was built with matches that of the give Lean installation. -/
def verifyLeanVersion (leanInstall : LeanInstall) : Except CliError PUnit := do
  unless leanInstall.githash == Lean.githash do
    throw <| CliError.leanRevMismatch Lean.githash leanInstall.githash

/-- Output the detected installs and verify the Lean version. -/
def verifyInstall (opts : LakeOptions) : ExceptT CliError MainM PUnit := do
  IO.println s!"Lean:\n{repr <| opts.leanInstall?}"
  IO.println s!"Lake:\n{repr <| opts.lakeInstall?}"
  let (leanInstall, _) ← getInstall opts
  verifyLeanVersion leanInstall

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
def printPaths (config : LakeConfig) (imports : List String := []) : MainM PUnit := do
  let configFile := config.rootDir / config.configFile
  if (← configFile.pathExists) then
    if (← IO.getEnv invalidConfigEnvVar) matches some .. then
      IO.eprintln s!"Error parsing '{configFile}'.  Please restart the lean server after fixing the Lake configuration file."
      exit 1
    let ws ← loadWorkspace config
    let ctx ← mkBuildContext ws config.leanInstall config.lakeInstall
    ws.root.buildImportsAndDeps imports |>.run MonadLog.eio ctx
    IO.println <| Json.compress <| toJson ws.leanPaths
  else
    exit noConfigFileCode

def env (cmd : String) (args : Array String := #[]) : LakeT IO UInt32 := do
  IO.Process.spawn {cmd, args, env := ← getLeanEnv} >>= (·.wait)

def serve (args : Array String) : LakeT IO UInt32 := do
  let (extraEnv, moreServerArgs) ←
    try
      pure (← getLeanEnv, (← getWorkspace).root.moreServerArgs)
    catch _ =>
      pure (#[(invalidConfigEnvVar, "1")], #[])
  (← IO.Process.spawn {
    cmd := (← getLean).toString
    args := #["--server"] ++ moreServerArgs ++ args
    env := extraEnv
  }).wait

def parseScriptSpec (ws : Workspace) (spec : String) : Except CliError (Package × String) :=
  match spec.splitOn "/" with
  | [script] => return (ws.root, script)
  | [pkg, script] => return (← parsePackageSpec ws pkg, script)
  | _ => throw <| CliError.invalidScriptSpec spec

def script : (cmd : String) → CliM PUnit
| "list" => do
  processOptions lakeOption
  let config ← mkLakeConfig (← getThe LakeOptions)
  noArgsRem do
    let ws ← loadWorkspace config
    ws.packageMap.forM fun name pkg => do
    let pkgName := pkg.name.toString (escape := false)
    pkg.scripts.forM fun name script =>
      let scriptName := name.toString (escape := false)
      IO.println s!"{pkgName}/{scriptName}"
| "run" => do
  processOptions lakeOption
  let spec ← takeArg "script spec"; let args ← takeArgs
  let config ← mkLakeConfig (← getThe LakeOptions)
  let ws ← loadWorkspace config
  let (pkg, scriptName) ← parseScriptSpec ws spec
  if let some script := pkg.scripts.find? scriptName then
    exit <| ← script.run args |>.run {
      lean := config.leanInstall,
      lake := config.lakeInstall,
      opaqueWs := ws
    }
  else do
    throw <| CliError.unknownScript scriptName
| "doc" => do
  processOptions lakeOption
  let spec ← takeArg "script spec"
  let config ← mkLakeConfig (← getThe LakeOptions)
  noArgsRem do
    let ws ← loadWorkspace config
    let (pkg, scriptName) ← parseScriptSpec ws spec
    if let some script := pkg.scripts.find? scriptName then
      match script.doc? with
      | some doc => IO.println doc
      | none => throw <| CliError.missingScriptDoc scriptName
    else
      throw <| CliError.unknownScript scriptName
| "help" => do
  IO.println <| helpScript <| (← takeArg?).getD ""
| cmd =>
  throw <| CliError.unknownCommand cmd

def command : (cmd : String) → CliM PUnit
| "new" => do
  processOptions lakeOption
  let pkgName ← takeArg "package name"
  noArgsRem <| new pkgName
| "init" => do
  processOptions lakeOption
  let pkgName ← takeArg "package name"
  noArgsRem <| init pkgName
| "build" => do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLakeConfig opts opts.subArgs
  let ws ← loadWorkspace config
  let targetSpecs ← takeArgs
  let target ← show Except _ _ from do
    let targets ← targetSpecs.mapM <| parseTargetSpec ws
    if targets.isEmpty then
      resolveDefaultPackageTarget ws.root
    else
      return Target.collectOpaqueList targets
  let ctx ← mkBuildContext ws config.leanInstall config.lakeInstall
  BuildM.run MonadLog.io ctx target.build
| "update" => do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLakeConfig opts opts.subArgs
  noArgsRem <| discard <| loadWorkspace config (updateDeps := true)
| "print-paths" => do
  processOptions lakeOption
  let config ← mkLakeConfig (← getThe LakeOptions)
  printPaths config (← takeArgs)
| "clean" => do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLakeConfig opts opts.subArgs
  noArgsRem <| (← loadPkg config).clean
| "script" => do
  if let some cmd ← takeArg? then
    processLeadingOptions lakeOption -- between command and args
    if (← getWantsHelp) then
      IO.println <| helpScript cmd
    else
      script cmd
  else
    throw <| CliError.missingCommand
| "serve" => do
  processOptions lakeOption
  let args := (← getThe LakeOptions).subArgs.toArray
  noArgsRem do exit <| ← runLakeT <| serve args
| "env" => do
  let cmd ← takeArg "command"; let args ← takeArgs
  exit <| ← runLakeT <| env cmd args.toArray
| "self-check"  => do
  processOptions lakeOption
  noArgsRem <| verifyInstall (← getThe LakeOptions)
| "help" => do
  IO.println <| help <| (← takeArg?).getD ""
| cmd =>
  throw <| CliError.unknownCommand cmd

def processArgs : CliM PUnit := do
  match (← getArgs) with
  | [] => IO.println usage
  | ["--version"] => IO.println uiVersionString
  | _ => -- normal CLI
    processLeadingOptions lakeOption -- between `lake` and command
    if let some cmd ← takeArg? then
      processLeadingOptions lakeOption -- between command and args
      if (← getWantsHelp) then
        IO.println <| help cmd
      else
        command cmd
    else
      if (← getWantsHelp) then
        IO.println usage
      else
        throw <| CliError.missingCommand

end Cli

open Cli in
def CliM.run (self : CliM α) (args : List String) : BaseIO UInt32 := do
  let (leanInstall?, lakeInstall?) ← findInstall?
  let main := self args |>.run' {leanInstall?, lakeInstall?}
  let main := main.run >>= fun | .ok a => pure a | .error e => error e.toString
  main.run

def cli (args : List String) : BaseIO UInt32 :=
  Cli.processArgs.run args
