/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Util.Paths
import Lake.Init
import Lake.Help
import Lake.BuildBin
import Lake.LeanConfig
import Lake.SearchPath
import Lake.InstallPath
import Lake.CliT

open System
open Lean (LeanPaths toJson)

namespace Lake

-- # Utilities

def Package.run (script : String) (args : List String) (self : Package) : IO UInt32 :=
  if let some script := self.scripts.find? script then
    script args
  else do
    throw <| IO.userError s!"unknown script {script}"

def Package.clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir

-- # CLI

structure CliState where
  rootDir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  leanInstall? : Option LeanInstall := none
  lakeInstall? : Option LakeInstall := none
  subArgs : List String := []
  wantsHelp : Bool := false

abbrev CliM := CliT <| StateT CliState <| EIO UInt32

namespace Cli
open CliT

-- ## Basic Actions

/-- Perform an IO action and silently exit with the given code (default: 1) if it errors. -/
def runIO' (x : IO α) (rc : UInt32 := 1) : CliM α :=
  x.toEIO fun e => rc

/-- Exit the CLI with given return code (i.e., throw it). -/
def exit (rc : UInt32) : CliM α := do
  throw rc

/-- Print out a line wih the given message and then exit with an error code. -/
def error (msg : String) (rc : UInt32 := 1) : CliM α := do
  runIO' <| IO.eprintln s!"error: {msg}"
  exit rc

/-- Print out a line wih the given message. -/
def output (msg : String) : CliM PUnit :=
  runIO' <| IO.println msg

/--
  Perform an IO action.
  If it throws an error, invoke `error` with the its message.
-/
def runIO (x : IO α) : CliM α := do
  match (← runIO' x.toIO') with
  | Except.ok a => pure a
  | Except.error e => error (toString e)

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

def getLeanInstall? : CliM (Option LeanInstall) :=
  (·.leanInstall?) <$> getThe CliState

def getLakeInstall? : CliM (Option LakeInstall) :=
  (·.lakeInstall?) <$> getThe CliState

-- ## Complex Actions

def loadPkg (args : List String) : CliM Package := do
  let dir ← getRootDir; let file ← getConfigFile
  runIO <| setupLeanSearchPath (← getLeanInstall?) (← getLakeInstall?)
  runIO <| Package.load dir args (dir / file)

/-- Get the Lean and Lake installation. Error if either is missing. -/
def getInstall : CliM (LeanInstall × LakeInstall) := do
  if let some leanInstall ← getLeanInstall? then
    if let some lakeInstall ← getLakeInstall? then
      return (leanInstall, lakeInstall)
    else
      error "could not detect the configuration of the Lake installation"
  else
    error "could not detect a Lean installation"

/-- Perform the given build action using information from CLI. -/
def runBuildM (x : BuildM α) : CliM α := do
  let (leanInstall, lakeInstall) ← getInstall
  runIO <| x.runIn {
    leanInstall, lakeInstall
    methodsRef := BuildMethodsRef.mk {
      logInfo  := fun msg => IO.println msg
      logError := fun msg => IO.eprintln msg
    }
  }

/-- Variant of `runBuildM` that discards the build monad's output. -/
def runBuildM_ (x : BuildM α) : CliM PUnit :=
  discard <| runBuildM x

-- ## Argument Parsing

def takeArg : CliM String := do
  let arg? ← takeArg?
  match arg? with
  | none => error "missing argument"
  | some arg => arg

def takeFileArg : CliM FilePath := do
  match (← takeArg?) with
  | none => error "missing file argument"
  | some arg => arg

/--
  Verify that there are no CLI arguments remaining
  before running the given action.
-/
def noArgsRem (act : CliM α) : CliM α := do
  let args ← takeArgs
  if args.isEmpty then act else
    error s!"unexpected arguments: {" ".intercalate args}"

-- ## Option Parsing

def unknownShortOption (opt : Char) : CliM PUnit :=
  error s!"unknown short option '-{opt}'"

def shortOption : (opt : Char) → CliM PUnit
| 'h' => setWantsHelp
| 'd' => do setRootDir (← takeFileArg)
| 'f' => do setConfigFile (← takeFileArg)
| opt => unknownShortOption opt

def unknownLongOption (opt : String) : CliM PUnit :=
  error s!"unknown long option '{opt}'"

def longOption : (opt : String) → CliM PUnit
| "--help"  => setWantsHelp
| "--dir"   => do setRootDir (← takeFileArg)
| "--file"  => do setConfigFile (← takeFileArg)
| "--"      => do setSubArgs (← takeArgs)
| opt       => unknownLongOption opt

-- ## Commands

/-- Run the given script from the given package with the given arguments. -/
def script (pkg : Package) (name : String) (args : List String) :  CliM UInt32 := do
  if let some script := pkg.scripts.find? name then
    runIO (script args)
  else
    pkg.scripts.forM (m := CliM) fun name _ => do
      output <| name.toString (escape := false)
    error s!"unknown script '{name}'"

/-- Verify the Lean version Lake was built with matches that of the Lean installation. -/
def verifyLeanVersion : CliM PUnit := do
  if let some leanInstall ← getLeanInstall? then
    let out ← runIO <| IO.Process.output {
      cmd := leanInstall.lean.toString,
      args := #["--version"]
    }
    if out.exitCode == 0 then
      unless out.stdout.drop 14 |>.startsWith uiLeanVersionString do
        error s!"expected {uiLeanVersionString}, but got {out.stdout.trim}"
    else
      error s!"running `lean --version` exited with code {out.exitCode}"
  else
    error "no lean installation detected"

/-- Output the detected installs and verify the Lean version. -/
def verifyInstall : CliM PUnit := do
  output s!"Lean:\n{repr <| ← getLeanInstall?}"
  output s!"Lake:\n{repr <| ← getLakeInstall?}"
  verifyLeanVersion

/-- Exit code to return if `print-paths` cannot find the config file. -/
def noConfigFileCode : UInt32 := 2

/--
  Build a list of imports of the package
  and print the `.olean` and source directories of every used package.
  If no configuration file exists, exit silently with `noConfigFileCode` (i.e, 2).

  The `print-paths` command is used internally by Lean 4 server.
-/
def printPaths (imports : List String := []) : CliM PUnit := do
  let erc := 2
  let (leanInstall, lakeInstall) ← getInstall
  let configFile := (← getRootDir) / (← getConfigFile)
  if (← runIO' configFile.pathExists noConfigFileCode) then
    let pkg ← loadPkg (← getSubArgs)
    runIO do
      let pkgs ← pkg.buildImportsAndDeps imports |>.runIn {
        leanInstall, lakeInstall
        methodsRef := BuildMethodsRef.mk {
          logInfo  := fun msg => IO.eprintln msg
          logError := fun msg => IO.eprintln msg
        }
      }
      IO.println <| toJson {
        oleanPath := pkgs.map (·.oleanDir),
        srcPath := pkgs.map (·.srcDir) : LeanPaths
      }
  else
    exit noConfigFileCode

def command : (cmd : String) → CliM PUnit
| "new"         => do noArgsRem <| runIO <| new (← takeArg)
| "init"        => do noArgsRem <| runIO <| init (← takeArg)
| "run"         => do exit <| ← noArgsRem <| script (← loadPkg []) (← takeArg) (← getSubArgs)
| "configure"   => do noArgsRem <| runBuildM_ (← loadPkg (← getSubArgs)).buildDeps
| "print-paths" => do noArgsRem <| printPaths (← takeArgs)
| "build"       => do noArgsRem <| runBuildM_ (← loadPkg (← getSubArgs)).build
| "build-lib"   => do noArgsRem <| runBuildM_ (← loadPkg (← getSubArgs)).buildLib
| "build-bin"   => do noArgsRem <| runBuildM_ (← loadPkg (← getSubArgs)).buildBin
| "clean"       => do noArgsRem <| runIO <| (← loadPkg (← getSubArgs)).clean
| "help"        => do output <| help (← takeArg?)
| "self-check"  => noArgsRem <| verifyInstall
| cmd           => error s!"unknown command '{cmd}'"

def processArgs : CliM PUnit := do
  match (← getArgs) with
  | [] => output usage
  | ["--version"] => output uiVersionString
  | _ => -- normal CLI
    processOptions
    if let some cmd ← takeArg? then
      if (← getWantsHelp) then output (help cmd) else
        command cmd
    else
      if (← getWantsHelp) then output usage else error "expected command"

end Cli

open Cli in
def CliM.run (self : CliM α) (args : List String) : IO UInt32 := do
  let (leanInstall?, lakeInstall?) ← findInstall?
  let initSt := {leanInstall?, lakeInstall?}
  let methods := {
    shortOption, longOption,
    longShortOption := unknownLongOption,
  }
  match (← CliT.run self args methods |>.run' initSt |>.toIO') with
  | Except.ok _ => pure 0
  | Except.error rc => pure rc

def cli (args : List String) : IO UInt32 :=
  Cli.processArgs.run args
