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
import Lake.Util.CliT
import Lake.CLI.Init
import Lake.CLI.Help
import Lake.CLI.Build

open System
open Lean (Name Json toJson)

namespace Lake

-- # CLI

structure CliState where
  rootDir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  leanInstall? : Option LeanInstall := none
  lakeInstall? : Option LakeInstall := none
  subArgs : List String := []
  wantsHelp : Bool := false

abbrev CliM := CliT <| StateT CliState MainM

namespace Cli
open CliT

-- ## Basic Actions

/-- Print out a line wih the given message and then exit with an error code. -/
protected def error (msg : String) (rc : UInt32 := 1) : CliM α := do
  IO.eprintln s!"error: {msg}" |>.catchExceptions fun _ => ()
  exit rc

instance : MonadError CliM := ⟨Cli.error⟩
instance : MonadLift IO CliM := ⟨MonadError.runIO⟩

-- ## State Management

def getRootDir : CliM FilePath :=
  (·.rootDir) <$> getThe CliState

def setRootDir (dir : FilePath) : CliM PUnit :=
  modifyThe CliState fun st => {st with rootDir := dir}

def getConfigFile : CliM FilePath :=
  (·.configFile) <$> getThe CliState

def setConfigFile (file : FilePath) : CliM PUnit :=
  modifyThe CliState fun st => {st with configFile := file}

def getSubArgs : CliM (List String) :=
  (·.subArgs) <$> getThe CliState

def setSubArgs (args : List String) : CliM PUnit :=
  modifyThe CliState fun st => {st with subArgs := args}

def getWantsHelp : CliM Bool :=
  (·.wantsHelp) <$> getThe CliState

def setWantsHelp : CliM PUnit :=
  modifyThe CliState fun st => {st with wantsHelp := true}

def setLean (lean : String) : CliM PUnit := do
  let leanInstall? ← findLeanCmdInstall? lean
  modifyThe CliState fun st => {st with leanInstall?}

def getLeanInstall? : CliM (Option LeanInstall) :=
  (·.leanInstall?) <$> getThe CliState

def getLakeInstall? : CliM (Option LakeInstall) :=
  (·.lakeInstall?) <$> getThe CliState

-- ## Complex Actions

def loadPkg (args : List String) : CliM Package := do
  let dir ← getRootDir; let file ← getConfigFile
  setupLeanSearchPath (← getLeanInstall?) (← getLakeInstall?)
  Package.load dir args (dir / file)

def loadConfig (args : List String) : CliM (Workspace × Package) := do
  let pkg ← loadPkg args
  let ws ← Workspace.ofPackage pkg
  let packageMap ← resolveDeps ws pkg |>.run LogMethods.eio (m := IO)
  let packageMap := packageMap.insert pkg.name pkg
  ({ws with packageMap}, pkg)

/-- Get the Lean installation. Error if missing. -/
def getLeanInstall : CliM LeanInstall := do
  if let some leanInstall ← getLeanInstall? then
    return leanInstall
  else
    error "could not detect a Lean installation"

/-- Get the Lake installation. Error if missing. -/
def getLakeInstall : CliM LakeInstall := do
  if let some lakeInstall ← getLakeInstall? then
    return lakeInstall
  else
    error "could not detect the configuration of the Lake installation"

/-- Get the Lean and Lake installation. Error if either is missing. -/
def getInstall : CliM (LeanInstall × LakeInstall) := do
  return (← getLeanInstall, ← getLakeInstall)

/-- Perform the given build action using information from CLI. -/
def runBuildM (ws : Workspace) (x : BuildM α) : CliM α := do
  let (leanInstall, lakeInstall) ← getInstall
  let ctx ← mkBuildContext ws leanInstall lakeInstall
  x.run LogMethods.io ctx

/-- Variant of `runBuildM` that discards the build monad's output. -/
def runBuildM_ (ws : Workspace) (x : BuildM α) : CliM PUnit :=
  discard <| runBuildM ws x

-- ## Argument Parsing

def takeArg (errMsg : String := "missing argument") : CliM String := do
  match (← takeArg?) with
  | none => error errMsg
  | some arg => arg

/--
Verify that there are no CLI arguments remaining
before running the given action.
-/
def noArgsRem (act : CliM α) : CliM α := do
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

/-- Splits a long option of the form `--long=arg` into `--long arg`. -/
def longOptionOrEq (optStr : String) : CliM PUnit :=
  let eqPos := optStr.posOf '='
  let arg := optStr.drop eqPos.succ
  let opt := optStr.take eqPos
  if arg.isEmpty then
    longOption opt
  else do
    consArg arg
    longOption opt

-- ## Commands

/-- Run the given script from the given package with the given arguments. -/
def script (pkg : Package) (name : String) (args : List String) :  CliM PUnit := do
  if let some script := pkg.scripts.find? name then
    if (← getWantsHelp) then
      if let some doc := script.doc? then
        IO.print doc
      else
        error s!"no documentation provided for `{name}`"
    else
      exit (← script.run args)
  else
    pkg.scripts.forM (m := CliM) fun name _ => do
      IO.println <| name.toString (escape := false)
    error s!"unknown script '{name}'"

/-- Verify the Lean version Lake was built with matches that of the Lean installation. -/
def verifyLeanVersion : CliM PUnit := do
  let leanInstall ← getLeanInstall
  let out ← IO.Process.output {
    cmd := leanInstall.lean.toString,
    args := #["--githash"]
  }
  if out.exitCode == 0 then
    let githash := out.stdout.trim
    unless githash == Lean.githash do
      error s!"expected Lean commit {Lean.githash}, but got {githash}"
  else
    error s!"running `lean --githash` exited with code {out.exitCode}"

/-- Output the detected installs and verify the Lean version. -/
def verifyInstall : CliM PUnit := do
  IO.println s!"Lean:\n{repr <| ← getLeanInstall?}"
  IO.println s!"Lake:\n{repr <| ← getLakeInstall?}"
  verifyLeanVersion

/-- Exit code to return if `print-paths` cannot find the config file. -/
def noConfigFileCode : ExitCode := 2

/--
Build a list of imports of the package
and print the `.olean` and source directories of every used package.
If no configuration file exists, exit silently with `noConfigFileCode` (i.e, 2).

The `print-paths` command is used internally by Lean 4 server.
-/
def printPaths (imports : List String := []) : CliM PUnit := do
  let (leanInstall, lakeInstall) ← getInstall
  let configFile := (← getRootDir) / (← getConfigFile)
  if (← configFile.pathExists) then
    let (ws, pkg) ← loadConfig (← getSubArgs)
    let ctx ← mkBuildContext ws leanInstall lakeInstall
    pkg.buildImportsAndDeps imports |>.run LogMethods.eio ctx
    IO.println <| Json.compress <| toJson ws.leanPaths
  else
    exit noConfigFileCode

def serve (leanInstall : LeanInstall)
(pkg : Package) (args : List String) : CliM PUnit := do
  let child ← IO.Process.spawn {
    cmd := leanInstall.lean.toString,
    args := #["--server"] ++ pkg.moreServerArgs ++ args
  }
  exit (← child.wait)

def env (leanInstall : LeanInstall) (ws : Workspace)
(cmd : String) (args : Array String) : CliM PUnit := do
  let child ← IO.Process.spawn {
    cmd, args,
    env := #[
      ("LEAN_SYSROOT", leanInstall.home.toString),
      ("LEAN_PATH", ws.oleanPath.toString),
      ("LEAN_SRC_PATH", ws.leanSrcPath.toString)
    ]
  }
  exit (← child.wait)

def command : (cmd : String) → CliM PUnit
| "new"         => do processOptions; noArgsRem <| new (← takeArg "missing package name")
| "init"        => do processOptions; noArgsRem <| init (← takeArg "missing package name")
| "run"         => do processOptions; noArgsRem <| script (← loadPkg []) (← takeArg "missing script") (← getSubArgs)
| "env"         => do env (← getLeanInstall) (← loadConfig []).1 (← takeArg "missing command") (← takeArgs).toArray
| "serve"       => do processOptions; noArgsRem <| serve (← getLeanInstall) (← loadPkg []) (← getSubArgs)
| "configure"   => do processOptions; let (ws, pkg) ← loadConfig (← getSubArgs); noArgsRem <| runBuildM ws pkg.buildDepOleans
| "print-paths" => do processOptions; printPaths (← takeArgs)
| "build"       => do processOptions; let (ws, pkg) ← loadConfig (← getSubArgs); runBuildM ws <| build pkg (← takeArgs)
| "clean"       => do processOptions; noArgsRem <| (← loadPkg (← getSubArgs)).clean
| "self-check"  => do processOptions; noArgsRem <| verifyInstall
| "help"        => do IO.println <| help (← takeArg?)
| cmd           => error s!"unknown command '{cmd}'"

def processArgs : CliM PUnit := do
  match (← getArgs) with
  | [] => IO.println usage
  | ["--version"] => IO.println uiVersionString
  | _ => -- normal CLI
    processLeadingOptions -- between `lake` and command
    if let some cmd ← takeArg? then
      processLeadingOptions -- between command and args
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
  let initSt := {leanInstall?, lakeInstall?}
  let methods := {
    shortOption,
    longOption := longOptionOrEq,
    longShortOption := unknownLongOption,
  }
  match (← CliT.run self args methods |>.run' initSt |>.toIO') with
  | Except.ok _ => pure 0
  | Except.error rc => pure rc

def cli (args : List String) : IO UInt32 :=
  Cli.processArgs.run args
