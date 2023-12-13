/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load
import Lake.Build.Imports
import Lake.Util.Error
import Lake.Util.MainM
import Lake.Util.Cli
import Lake.CLI.Init
import Lake.CLI.Help
import Lake.CLI.Build
import Lake.CLI.Error
import Lake.CLI.Actions
import Lake.CLI.Serve

-- # CLI

open System
open Lean (Json toJson fromJson? LeanPaths)

namespace Lake

/-! ## General options for top-level `lake` -/

structure LakeOptions where
  rootDir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  elanInstall? : Option ElanInstall := none
  leanInstall? : Option LeanInstall := none
  lakeInstall? : Option LakeInstall := none
  configOpts : NameMap String := {}
  subArgs : List String := []
  wantsHelp : Bool := false
  verbosity : Verbosity := .normal
  updateDeps : Bool := false
  reconfigure : Bool := false
  oldMode : Bool := false
  trustHash : Bool := true
  noBuild : Bool := false

/-- Get the Lean installation. Error if missing. -/
def LakeOptions.getLeanInstall (opts : LakeOptions) : Except CliError LeanInstall :=
  match opts.leanInstall? with
  | none => .error CliError.unknownLeanInstall
  | some lean => .ok lean

/-- Get the Lake installation. Error if missing. -/
def LakeOptions.getLakeInstall (opts : LakeOptions) : Except CliError LakeInstall :=
  match opts.lakeInstall? with
  | none => .error CliError.unknownLakeInstall
  | some lake => .ok lake

/-- Get the Lean and Lake installation. Error if either is missing. -/
def LakeOptions.getInstall (opts : LakeOptions) : Except CliError (LeanInstall × LakeInstall) := do
  return (← opts.getLeanInstall, ← opts.getLakeInstall)

/-- Compute the Lake environment based on `opts`. Error if an install is missing. -/
def LakeOptions.computeEnv (opts : LakeOptions) : EIO CliError Lake.Env := do
  Env.compute (← opts.getLakeInstall) (← opts.getLeanInstall) opts.elanInstall?
    |>.adaptExcept fun msg => .invalidEnv msg

/-- Make a `LoadConfig` from a `LakeOptions`. -/
def LakeOptions.mkLoadConfig (opts : LakeOptions) : EIO CliError LoadConfig :=
  return {
    env := ← opts.computeEnv
    rootDir := opts.rootDir
    configFile := opts.rootDir / opts.configFile
    configOpts := opts.configOpts
    leanOpts := Lean.Options.empty
    reconfigure := opts.reconfigure
  }

/-- Make a `BuildConfig` from a `LakeOptions`. -/
def LakeOptions.mkBuildConfig (opts : LakeOptions) : BuildConfig where
  oldMode := opts.oldMode
  trustHash := opts.trustHash
  noBuild := opts.noBuild

export LakeOptions (mkLoadConfig mkBuildConfig)

/-! ## Monad -/

abbrev CliMainM := ExceptT CliError MainM
abbrev CliStateM := StateT LakeOptions CliMainM
abbrev CliM := ArgsT CliStateM

def CliM.run (self : CliM α) (args : List String) : BaseIO ExitCode := do
  let (elanInstall?, leanInstall?, lakeInstall?) ← findInstall?
  let main := self.run' args |>.run' {elanInstall?, leanInstall?, lakeInstall?}
  let main := main.run >>= fun | .ok a => pure a | .error e => error e.toString
  main.run

instance : MonadLift LogIO CliStateM :=
  ⟨fun x => do MainM.runLogIO x (← get).verbosity⟩

instance : MonadLift OptionIO MainM where
  monadLift x := x.adaptExcept (fun _ => 1)

/-! ## Argument Parsing -/

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

/-! ## Option Parsing -/

def getWantsHelp : CliStateM Bool :=
  (·.wantsHelp) <$> get

def setLean (lean : String) : CliStateM PUnit := do
  let leanInstall? ← findLeanCmdInstall? lean
  modify ({·  with leanInstall?})

def setConfigOpt (kvPair : String) : CliM PUnit :=
  let pos := kvPair.posOf '='
  let (key, val) :=
    if pos = kvPair.endPos then
      (kvPair.toName, "")
    else
      (kvPair.extract 0 pos |>.toName, kvPair.extract (kvPair.next pos) kvPair.endPos)
  modifyThe LakeOptions fun opts =>
    {opts with configOpts := opts.configOpts.insert key val}

def lakeShortOption : (opt : Char) → CliM PUnit
| 'q' => modifyThe LakeOptions ({· with verbosity := .quiet})
| 'v' => modifyThe LakeOptions ({· with verbosity := .verbose})
| 'd' => do let rootDir ← takeOptArg "-d" "path"; modifyThe LakeOptions ({· with rootDir})
| 'f' => do let configFile ← takeOptArg "-f" "path"; modifyThe LakeOptions ({· with configFile})
| 'K' => do setConfigOpt <| ← takeOptArg "-K" "key-value pair"
| 'U' => modifyThe LakeOptions ({· with updateDeps := true})
| 'R' => modifyThe LakeOptions ({· with reconfigure := true})
| 'h' => modifyThe LakeOptions ({· with wantsHelp := true})
| 'H' => modifyThe LakeOptions ({· with trustHash := false})
| opt => throw <| CliError.unknownShortOption opt

def lakeLongOption : (opt : String) → CliM PUnit
| "--quiet"       => modifyThe LakeOptions ({· with verbosity := .quiet})
| "--verbose"     => modifyThe LakeOptions ({· with verbosity := .verbose})
| "--update"      => modifyThe LakeOptions ({· with updateDeps := true})
| "--reconfigure" => modifyThe LakeOptions ({· with reconfigure := true})
| "--old"         => modifyThe LakeOptions ({· with oldMode := true})
| "--no-build"    => modifyThe LakeOptions ({· with noBuild := true})
| "--rehash"      => modifyThe LakeOptions ({· with trustHash := false})
| "--dir"         => do let rootDir ← takeOptArg "--dir" "path"; modifyThe LakeOptions ({· with rootDir})
| "--file"        => do let configFile ← takeOptArg "--file" "path"; modifyThe LakeOptions ({· with configFile})
| "--lean"        => do setLean <| ← takeOptArg "--lean" "path or command"
| "--help"        => modifyThe LakeOptions ({· with wantsHelp := true})
| "--"            => do let subArgs ← takeArgs; modifyThe LakeOptions ({· with subArgs})
| opt             =>  throw <| CliError.unknownLongOption opt

def lakeOption :=
  option {
    short := lakeShortOption
    long := lakeLongOption
    longShort := shortOptionWithArg lakeShortOption
  }

/-! ## Actions -/

/-- Verify the Lean version Lake was built with matches that of the give Lean installation. -/
def verifyLeanVersion (leanInstall : LeanInstall) : Except CliError PUnit := do
  unless leanInstall.githash == Lean.githash do
    throw <| CliError.leanRevMismatch Lean.githash leanInstall.githash

/-- Output the detected installs and verify the Lean version. -/
def verifyInstall (opts : LakeOptions) : ExceptT CliError MainM PUnit := do
  IO.println s!"Elan:\n{repr <| opts.elanInstall?}"
  IO.println s!"Lean:\n{repr <| opts.leanInstall?}"
  IO.println s!"Lake:\n{repr <| opts.lakeInstall?}"
  let (leanInstall, _) ← opts.getInstall
  verifyLeanVersion leanInstall

def parseScriptSpec (ws : Workspace) (spec : String) : Except CliError Script :=
  match spec.splitOn "/" with
  | [scriptName] =>
    match ws.findScript? scriptName with
    | some script => return script
    | none => throw <| CliError.unknownScript spec
  | [pkg, scriptName] => do
    let pkg ← parsePackageSpec ws pkg
    match pkg.scripts.find? scriptName with
    | some script => return script
    | none => throw <| CliError.unknownScript spec
  | _ => throw <| CliError.invalidScriptSpec spec

def parseTemplateSpec (spec : String) : Except CliError InitTemplate :=
  if spec.isEmpty then
    pure default
  else if let some tmp := InitTemplate.parse? spec then
    pure tmp
  else
    throw <| CliError.unknownTemplate spec

/-! ## Commands -/

namespace lake

/-! ### `lake script` CLI -/

namespace script

protected def list : CliM PUnit := do
  processOptions lakeOption
  let config ← mkLoadConfig (← getThe LakeOptions)
  noArgsRem do
    let ws ← loadWorkspace config
    ws.packages.forM fun pkg => do
      pkg.scripts.forM fun _ script =>
        IO.println script.name

protected nonrec def run : CliM PUnit := do
  processLeadingOptions lakeOption  -- between `lake [script] run` and `<name>`
  let config ← mkLoadConfig (← getThe LakeOptions)
  let ws ← loadWorkspace config
  if let some spec ← takeArg? then
    let args ← takeArgs
    let script ← parseScriptSpec ws spec
    exit <| ← script.run args |>.run {opaqueWs := ws}
  else
    for script in ws.root.defaultScripts do
      exitIfErrorCode <| ← script.run [] |>.run {opaqueWs := ws}
    exit 0

protected def doc : CliM PUnit := do
  processOptions lakeOption
  let spec ← takeArg "script name"
  let config ← mkLoadConfig (← getThe LakeOptions)
  noArgsRem do
    let ws ← loadWorkspace config
    let script ← parseScriptSpec ws spec
    match script.doc? with
    | some doc => IO.println doc
    | none => throw <| CliError.missingScriptDoc script.name

protected def help : CliM PUnit := do
  IO.println <| helpScript <| (← takeArg?).getD ""

end script

def scriptCli : (cmd : String) → CliM PUnit
| "list"  => script.list
| "run"   => script.run
| "doc"   => script.doc
| "help"  => script.help
| cmd     => throw <| CliError.unknownCommand cmd

/-! ### `lake` CLI -/

protected def new : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let name ← takeArg "package name"
  let tmp ← parseTemplateSpec <| (← takeArg?).getD ""
  noArgsRem do MainM.runLogIO (new name tmp (← opts.computeEnv) opts.rootDir) opts.verbosity

protected def init : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let name := (← takeArg?).getD "."
  let tmp ← parseTemplateSpec <| (← takeArg?).getD ""
  noArgsRem do MainM.runLogIO (init name tmp (← opts.computeEnv) opts.rootDir) opts.verbosity

protected def build : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config opts.updateDeps
  let targetSpecs ← takeArgs
  let specs ← parseTargetSpecs ws targetSpecs
  let buildConfig := mkBuildConfig opts
  ws.runBuild (buildSpecs specs) buildConfig |>.run (MonadLog.io opts.verbosity)

protected def resolveDeps : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  noArgsRem do
    liftM <| discard <| (loadWorkspace config opts.updateDeps).run (MonadLog.io opts.verbosity)

protected def update : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let toUpdate := (← getArgs).foldl (·.insert <| stringToLegalOrSimpleName ·) {}
  liftM <| (updateManifest config toUpdate).run (MonadLog.io opts.verbosity)

protected def upload : CliM PUnit := do
  processOptions lakeOption
  let tag ← takeArg "release tag"
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config
  noArgsRem do
    liftM <| uploadRelease ws.root tag |>.run (MonadLog.io opts.verbosity)

protected def setupFile : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let loadConfig ← mkLoadConfig opts
  let buildConfig := mkBuildConfig opts
  let filePath ← takeArg "file path"
  let imports ← takeArgs
  setupFile loadConfig filePath imports buildConfig opts.verbosity

protected def clean : CliM PUnit := do
  processOptions lakeOption
  let config ← mkLoadConfig (← getThe LakeOptions)
  let ws ← loadWorkspace config
  let pkgSpecs ← takeArgs
  if pkgSpecs.isEmpty then
    ws.clean
  else
    let pkgs ← pkgSpecs.mapM fun pkgSpec =>
      match ws.findPackage? <| stringToLegalOrSimpleName pkgSpec with
      | none => throw <| .unknownPackage pkgSpec
      | some pkg => pure pkg.toPackage
    pkgs.forM (·.clean)

protected def script : CliM PUnit := do
  if let some cmd ← takeArg? then
    processLeadingOptions lakeOption -- between `lake script <cmd>` and args
    if (← getWantsHelp) then
      IO.println <| helpScript cmd
    else
      scriptCli cmd
  else
    throw <| CliError.missingCommand

protected def serve : CliM PUnit := do
  processOptions lakeOption
  let opts ← getThe LakeOptions
  let args := opts.subArgs.toArray
  let config ← mkLoadConfig opts
  noArgsRem do exit <| ← serve config args

protected def env : CliM PUnit := do
  let config ← mkLoadConfig (← getThe LakeOptions)
  let env ← do
    if (← config.configFile.pathExists) then
      pure (← loadWorkspace config).augmentedEnvVars
    else
      pure config.env.vars
  if let some cmd ← takeArg? then
    let child ← IO.Process.spawn {cmd, args := (← takeArgs).toArray, env}
    exit <| ← child.wait
  else
    env.forM fun (var, val?) =>
      IO.println s!"{var}={val?.getD ""}"
    exit 0

protected def exe : CliM PUnit := do
  let exeSpec ← takeArg "executable target"
  let args ← takeArgs
  let opts ← getThe LakeOptions
  let config ← mkLoadConfig opts
  let ws ← loadWorkspace config
  let exe ← parseExeTargetSpec ws exeSpec
  let exeFile ← ws.runBuild (exe.build >>= (·.await)) <| mkBuildConfig opts
  exit <| ← (env exeFile.toString args.toArray).run <| mkLakeContext ws

protected def selfCheck : CliM PUnit := do
  processOptions lakeOption
  noArgsRem do verifyInstall (← getThe LakeOptions)

protected def help : CliM PUnit := do
  IO.println <| help <| (← takeArg?).getD ""

end lake

def lakeCli : (cmd : String) → CliM PUnit
| "new"                 => lake.new
| "init"                => lake.init
| "build"               => lake.build
| "update" | "upgrade"  => lake.update
| "resolve-deps"        => lake.resolveDeps
| "upload"              => lake.upload
| "setup-file"          => lake.setupFile
| "clean"               => lake.clean
| "script"              => lake.script
| "scripts"             => lake.script.list
| "run"                 => lake.script.run
| "serve"               => lake.serve
| "env"                 => lake.env
| "exe" | "exec"        => lake.exe
| "self-check"          => lake.selfCheck
| "help"                => lake.help
| cmd                   => throw <| CliError.unknownCommand cmd

def lake : CliM PUnit := do
  match (← getArgs) with
  | [] => IO.println usage
  | ["--version"] => IO.println uiVersionString
  | _ => -- normal CLI
    processLeadingOptions lakeOption -- between `lake` and command
    if let some cmd ← takeArg? then
      processLeadingOptions lakeOption -- between `lake <cmd>` and args
      if (← getWantsHelp) then
        IO.println <| help cmd
      else
        lakeCli cmd
    else
      if (← getWantsHelp) then
        IO.println usage
      else
        throw <| CliError.missingCommand

def cli (args : List String) : BaseIO ExitCode :=
  inline <| (lake).run args
