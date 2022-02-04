/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/

import Lake.Config.Load
import Lake.Config.SearchPath
import Lake.Config.InstallPath
import Lake.Config.Resolve
import Lake.Config.Util
import Lake.Util.Error
import Lake.Util.MainM
import Lake.Util.Cli
import Lake.CLI.Init
import Lake.CLI.Help
import Lake.CLI.Build

open System
open Lean (Name Json toJson)

namespace Lake

-- # CLI

structure LakeOptions where
  rootDir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  leanInstall? : Option LeanInstall := none
  lakeInstall? : Option LakeInstall := none
  subArgs : List String := []
  wantsHelp : Bool := false

abbrev CliStateM := StateT LakeOptions <| MainM
abbrev CliM := ArgsT CliStateM

namespace Cli

-- ## Basic Actions

/-- Print out a line wih the given message and then exit with an error code. -/
protected def error (msg : String) (rc : UInt32 := 1) : MainM α := do
  IO.eprintln s!"error: {msg}" |>.catchExceptions fun _ => pure ()
  exit rc

instance : MonadError MainM := ⟨Cli.error⟩
instance : MonadLift IO MainM := ⟨MonadError.runIO⟩

-- ## Basic State Management

def getRootDir : CliStateM FilePath :=
  (·.rootDir) <$> get

def setRootDir (dir : FilePath) : CliStateM PUnit :=
  modify fun st => {st with rootDir := dir}

def getConfigFile : CliStateM FilePath :=
  (·.configFile) <$> get

def setConfigFile (file : FilePath) : CliStateM PUnit :=
  modify ({· with configFile := file})

def getSubArgs : CliStateM (List String) :=
  (·.subArgs) <$> get

def setSubArgs (args : List String) : CliStateM PUnit :=
  modify fun st => {st with subArgs := args}

def getWantsHelp : CliStateM Bool :=
  (·.wantsHelp) <$> get

def setWantsHelp : CliStateM PUnit :=
  modify fun st => {st with wantsHelp := true}

def setLean (lean : String) : CliStateM PUnit := do
  let leanInstall? ← findLeanCmdInstall? lean
  modify fun st => {st with leanInstall?}

def getLeanInstall? : CliStateM (Option LeanInstall) :=
  (·.leanInstall?) <$> get

def getLakeInstall? : CliStateM (Option LakeInstall) :=
  (·.lakeInstall?) <$> get

-- ## Complex State Management

def loadPkg (args : List String := []) : CliStateM Package := do
  let dir ← getRootDir; let file ← getConfigFile
  setupLeanSearchPath (← getLeanInstall?) (← getLakeInstall?)
  Package.load dir args (dir / file)

def loadWorkspace (args : List String := []) : CliStateM Workspace := do
  let pkg ← loadPkg args
  let ws := Workspace.ofPackage pkg
  let packageMap ← resolveDeps ws pkg |>.run LogMethods.eio (m := IO)
  let packageMap := packageMap.insert pkg.name pkg
  return {ws with packageMap}

/-- Get the Lean installation. Error if missing. -/
def getLeanInstall : CliStateM LeanInstall := do
  if let some leanInstall ← getLeanInstall? then
    return leanInstall
  else
    error "could not detect a Lean installation"

/-- Get the Lake installation. Error if missing. -/
def getLakeInstall : CliStateM LakeInstall := do
  if let some lakeInstall ← getLakeInstall? then
    return lakeInstall
  else
    error "could not detect the configuration of the Lake installation"

/-- Get the Lean and Lake installation. Error if either is missing. -/
def getInstall : CliStateM (LeanInstall × LakeInstall) := do
  return (← getLeanInstall, ← getLakeInstall)

/-- Perform the given build action using information from CLI. -/
def runBuildM (ws : Workspace) (x : BuildM α) : CliStateM α := do
  let (leanInstall, lakeInstall) ← getInstall
  let ctx ← mkBuildContext ws leanInstall lakeInstall
  x.run LogMethods.io ctx

/-- Variant of `runBuildM` that discards the build monad's output. -/
def runBuildM_ (ws : Workspace) (x : BuildM α) : CliStateM PUnit :=
  discard <| runBuildM ws x

-- ## Argument Parsing

def takeArg (errMsg : String := "missing argument") : CliM String := do
  match (← takeArg?) with
  | none => error errMsg
  | some arg => return arg

/--
Verify that there are no CLI arguments remaining
before running the given action.
-/
def noArgsRem (act : CliStateM α) : CliM α := do
  let args ← getArgs
  if args.isEmpty then act else
    error s!"unexpected arguments: {" ".intercalate args}"

-- ## Option Parsing

def unknownShortOption (opt : Char) : CliM PUnit :=
  error s!"unknown short option '-{opt}'"

def shortOption : (opt : Char) → CliM PUnit
| 'h' => setWantsHelp
| 'd' => do setRootDir <| ← takeArg "missing path after -d"
| 'f' => do setConfigFile <| ← takeArg "missing path after -f"
| opt => unknownShortOption opt

def unknownLongOption (opt : String) : CliM PUnit :=
  error s!"unknown long option '{opt}'"

def longOption : (opt : String) → CliM PUnit
| "--help"  => setWantsHelp
| "--dir"   => do setRootDir <| ← takeArg "missing path after --dir"
| "--file"  => do setConfigFile <| ← takeArg "missing path after --file"
| "--lean"  => do setLean <| ← takeArg "missing command after --lean"
| "--"      => do setSubArgs <| ← takeArgs
| opt       => unknownLongOption opt

def lakeOption :=
  option {
    short := shortOption
    long := longOption
    longShort := shortOptionWithArg shortOption
  }

-- ## Commands

def withContext [MonadLiftT m CliStateM] (x : LakeT m α) : CliStateM α := do
  let ws ← loadWorkspace
  let (lean, lake) ← getInstall
  liftM <| x |>.run {lean, lake, opaqueWs := ws}

/-- Verify the Lean version Lake was built with matches that of the Lean installation. -/
def verifyLeanVersion : CliStateM PUnit := do
  let lean ← getLeanInstall
  unless lean.githash == Lean.githash do
    let githash := if lean.githash.isEmpty then  "nothing" else lean.githash
    error s!"expected Lean commit {Lean.githash}, but got {lean.githash}"

/-- Output the detected installs and verify the Lean version. -/
def verifyInstall : CliStateM PUnit := do
  IO.println s!"Lean:\n{repr <| ← getLeanInstall?}"
  IO.println s!"Lake:\n{repr <| ← getLakeInstall?}"
  verifyLeanVersion

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
def printPaths (imports : List String := []) : CliStateM PUnit := do
  let (lean, lake) ← getInstall
  let configFile := (← getRootDir) / (← getConfigFile)
  if (← IO.getEnv invalidConfigEnvVar) matches some .. then
    IO.eprintln s!"Error parsing '{configFile}'.  Please restart the lean server after fixing the Lake configuration file."
    exit 1
  else if (← configFile.pathExists) then
    let ws ← loadWorkspace (← getSubArgs)
    let ctx ← mkBuildContext ws lean lake
    ws.root.buildImportsAndDeps imports |>.run LogMethods.eio ctx
    IO.println <| Json.compress <| toJson ws.leanPaths
  else
    exit noConfigFileCode

def env (cmd : String) (args : Array String := #[]) : LakeT IO UInt32 := do
  IO.Process.spawn {cmd, args, env := ← getLeanEnv} >>= (·.wait)

def serve (args : Array String) : CliStateM UInt32 := do
  let (lean, lake) ← getInstall
  let (extraEnv, moreServerArgs) ←
    try
      withContext (m := IO) <|
        return (← getLeanEnv, (← getWorkspace).root.moreServerArgs)
    catch _ =>
      pure (#[(invalidConfigEnvVar, "1")], #[])
  (← IO.Process.spawn {
    cmd := lean.lean.toString
    args := #["--server"] ++ moreServerArgs ++ args
    env := extraEnv
  }).wait

def parseScriptSpec (ws : Workspace) (spec : String) : IO (Package × String) :=
  match spec.splitOn "/" with
  | [script] => return (ws.root, script)
  | [pkg, script] => return (← parsePkgSpec ws pkg, script)
  | _ =>  error s!"invalid script spec '{spec}' (too many '/')"

def script : (cmd : String) → CliM PUnit
| "list" => do
  processOptions lakeOption
  noArgsRem <| (← loadWorkspace).packageMap.forM fun name pkg => do
    let pkgName := pkg.name.toString (escape := false)
    pkg.scripts.forM fun name script =>
      let scriptName := name.toString (escape := false)
      IO.println s!"{pkgName}/{scriptName}"
| "run" => do
  processOptions lakeOption
  let spec ← takeArg "missing script spec"; let args ← takeArgs
  exit <| ← withContext (m := IO) do
    let (pkg, script) ← parseScriptSpec (← getWorkspace) spec
    pkg.run script args
| "doc" => do
  processOptions lakeOption
  let spec ← takeArg "missing script spec"
  noArgsRem <| withContext (m := IO) do
    let (pkg, script) ← parseScriptSpec (← getWorkspace) spec
    pkg.printScriptDoc script
| "help" => do
  IO.println <| helpScript <| (← takeArg?).getD ""
| cmd =>
  error s!"unknown command '{cmd}'"

def command : (cmd : String) → CliM PUnit
| "new" => do
  processOptions lakeOption
  let pkgName ← takeArg "missing package name"
  noArgsRem <| new pkgName
| "init" => do
  processOptions lakeOption
  let pkgName ← takeArg "missing package name"
  noArgsRem <| init pkgName
| "build" => do
  processOptions lakeOption
  let ws ← loadWorkspace (← getSubArgs)
  runBuildM ws <| build (← takeArgs)
| "configure" => do
  processOptions lakeOption
  let ws ← loadWorkspace (← getSubArgs)
  noArgsRem <| runBuildM ws ws.root.buildDepOleans
| "print-paths" => do
  processOptions lakeOption
  printPaths (← takeArgs)
| "clean" => do
  processOptions lakeOption
  noArgsRem <| (← loadPkg (← getSubArgs)).clean
| "script" => do
  if let some cmd ← takeArg? then
    processLeadingOptions lakeOption -- between command and args
    if (← getWantsHelp) then
      IO.println <| helpScript cmd
    else
      script cmd
  else
    error "expected command"
| "serve" => do
  let args ← getSubArgs
  noArgsRem do exit (← serve args.toArray)
| "env" => do
  let cmd ← takeArg "missing command"; let args ← takeArgs
  exit <| ← withContext <| env cmd args.toArray
| "self-check"  => do
  processOptions lakeOption
  noArgsRem <| verifyInstall
| "help" => do
  IO.println <| help <| (← takeArg?).getD ""
| cmd =>
  error s!"unknown command '{cmd}'"

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
      if (← getWantsHelp) then IO.println usage else error "expected command"

end Cli

open Cli in
def CliM.run (self : CliM α) (args : List String) : IO UInt32 := do
  let (leanInstall?, lakeInstall?) ← findInstall?
  match (← self args |>.run' {leanInstall?, lakeInstall?} |>.toIO') with
  | Except.ok _ => pure 0
  | Except.error rc => pure rc

def cli (args : List String) : IO UInt32 :=
  Cli.processArgs.run args
