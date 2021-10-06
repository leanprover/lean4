/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Data.Json
import Lake.Init
import Lake.Help
import Lake.BuildBin
import Lake.LeanConfig
import Lake.SearchPath
import Lake.InstallPath
import Lake.CliT

open System
open Lean (Json)

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

structure CliOptions where
  wantsHelp : Bool := false
  dir : FilePath := "."
  configFile : FilePath := defaultConfigFile
  subArgs : List String := []
  leanInstall? : Option LeanInstall := none
  lakeInstall? : Option LakeInstall := none

abbrev CliM := CliT <| StateT CliOptions IO

namespace CliM
open CliT

-- ## State Management

def getDir : CliM FilePath :=
  CliOptions.dir <$> getThe CliOptions

def setDir (dir : FilePath) : CliM PUnit :=
  modifyThe CliOptions fun st => {st with dir := dir}

def getConfigFile : CliM FilePath :=
  CliOptions.configFile <$> getThe CliOptions

def setConfigFile (file : FilePath) : CliM PUnit :=
  modifyThe CliOptions fun st => {st with configFile := file}

def getSubArgs : CliM (List String) :=
  CliOptions.subArgs <$> getThe CliOptions

def setSubArgs (args : List String) : CliM PUnit :=
  modifyThe CliOptions fun st => {st with subArgs := args}

def getWantsHelp : CliM Bool :=
  CliOptions.wantsHelp <$> getThe CliOptions

def setWantsHelp : CliM PUnit :=
  modifyThe CliOptions fun st => {st with wantsHelp := true}

def getLeanInstall? : CliM (Option LeanInstall) :=
  CliOptions.leanInstall? <$> getThe CliOptions

def getLakeInstall? : CliM (Option LakeInstall) :=
  CliOptions.lakeInstall? <$> getThe CliOptions

def loadPkg (args : List String) : CliM Package := do
  let dir ← getDir; let file ← getConfigFile
  setupLeanSearchPath (← getLeanInstall?) (← getLakeInstall?)
  Package.load dir args (dir / file)

def takeArg : CliM String := do
  match (← takeArg?) with
  | none => throw <| IO.userError "missing argument"
  | some arg => arg

def takeFileArg : CliM FilePath := do
  match (← takeArg?) with
  | none => throw <| IO.userError "missing file argument"
  | some arg => arg

-- ## Option Parsing

def unknownShortOption (opt : Char) : CliM PUnit :=
  throw <| IO.userError s!"unknown short option '-{opt}'"

def shortOption : (opt : Char) → CliM PUnit
| 'h' => setWantsHelp
| 'd' => do setDir (← takeFileArg)
| 'f' => do setConfigFile (← takeFileArg)
| opt => unknownShortOption opt

def unknownLongOption (opt : String) : CliM PUnit :=
  throw <| IO.userError s!"unknown long option '{opt}'"

def longOption : (opt : String) → CliM PUnit
| "--help"  => setWantsHelp
| "--dir"   => do setDir (← takeFileArg)
| "--file"  => do setConfigFile (← takeFileArg)
| "--"      => do setSubArgs (← takeArgs)
| opt       => unknownLongOption opt

-- ## Actions

/-- Print out a line wih the given message and then return an error code. -/
def error (msg : String) (rc : UInt32 := 1) : CliM UInt32 := do
  IO.eprintln s!"error: {msg}"; rc

/-- Print out a line wih the given message and then return code 0. -/
def output (msg : String) : CliM UInt32 := do
  IO.println msg; pure 0

/--
  Perform the given IO action and then return code 0.
  If it throws an error, invoke `error` with the the error's message.
-/
def execIO (x : IO α) : CliM UInt32 := do
  try Functor.mapConst 0 x catch e => error (toString e)

/--
  Get the install configuration of Lean and Lake.
  Error if either could not be detected.
-/
def getInstall : CliM (LeanInstall × LakeInstall) := do
  if let some leanInstall ← getLeanInstall? then
    if let some lakeInstall ← getLakeInstall? then
      return (leanInstall, lakeInstall)
    else
      throw <| IO.userError <|
        "could not detect the configuration of the Lake installation"
  else
    throw <| IO.userError <| "could not detect a Lean installation"

/--
  Perform the given build action and then return code 0.
  If it throws an error, invoke `error` with the the error's message.
-/
def execBuild (x : BuildM α) : CliM UInt32 := do
  try
    let (leanInstall, lakeInstall) ← getInstall
    execIO do
      x.runIn {
        leanInstall, lakeInstall
        methodsRef := BuildMethodsRef.mk {
          logInfo  := fun msg => IO.println msg
          logError := fun msg => IO.eprintln msg
        }
      }
  catch e =>
    error (toString e)

/-- Run the given script from the given package with the given arguments. -/
def script (pkg : Package) (name : String) (args : List String) :  CliM UInt32 := do
  if let some script := pkg.scripts.find? name then
    script args
  else
    pkg.scripts.forM fun name _ => IO.println name
    error s!"unknown script '{name}'"

def noArgsRem (act : CliM UInt32) : CliM UInt32 := do
  let args ← takeArgs
  if args.isEmpty then act else
    error s!"unexpected arguments: {" ".intercalate args}"

def verifyLeanVersion : CliM UInt32 := do
  if let some leanInstall ← getLeanInstall? then
    let out ← IO.Process.output {
      cmd := leanInstall.lean.toString,
      args := #["--version"]
    }
    if out.exitCode == 0 then
      if out.stdout.drop 14 |>.startsWith uiLeanVersionString then
        pure 0
      else
        error s!"expected {uiLeanVersionString}, but got {out.stdout.trim}"
    else
      error s!"running `lean --version` exited with code {out.exitCode}"
  else
    error "no lean installation detected"

def verifyInstall : CliM UInt32 := do
  IO.println s!"Lean:\n{repr <| ← getLeanInstall?}"
  IO.println s!"Lake:\n{repr <| ← getLakeInstall?}"
  verifyLeanVersion

def printPaths (pkg : Package) (imports : List String := []) : CliM UInt32 :=
   try
    let (leanInstall, lakeInstall) ← getInstall
    execIO do
      let deps ← pkg.buildImportsAndDeps imports |>.runIn {
        leanInstall, lakeInstall
        methodsRef := BuildMethodsRef.mk {
          logInfo  := fun msg => IO.eprintln msg
          logError := fun msg => IO.eprintln msg
        }
      }
      IO.println <| Json.compress <| Json.mkObj [
        ("LEAN_PATH", SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)),
        ("LEAN_SRC_PATH", SearchPath.toString <| pkg.srcDir :: deps.map (·.srcDir))
      ]
  catch e =>
    error (toString e)

def command : (cmd : String) → CliM UInt32
| "new"         => do noArgsRem <| execIO <| new (← takeArg)
| "init"        => do noArgsRem <| execIO <| init (← takeArg)
| "run"         => do noArgsRem <| script (← loadPkg []) (← takeArg) (← getSubArgs)
| "configure"   => do noArgsRem <| execBuild (← loadPkg (← getSubArgs)).buildDeps
| "print-paths" => do noArgsRem <| printPaths (← loadPkg (← getSubArgs)) (← takeArgs)
| "build"       => do noArgsRem <| execBuild (← loadPkg (← getSubArgs)).build
| "build-lib"   => do noArgsRem <| execBuild (← loadPkg (← getSubArgs)).buildLib
| "build-bin"   => do noArgsRem <| execBuild (← loadPkg (← getSubArgs)).buildBin
| "clean"       => do noArgsRem <| execIO <| (← loadPkg (← getSubArgs)).clean
| "help"        => do output <| help (← takeArg?)
| "self-check"  => noArgsRem <| verifyInstall
| cmd           => error s!"unknown command '{cmd}'"

def processArgs : CliM UInt32 := do
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

def run (self : CliM α) (args : List String) : IO α := do
  let (leanInstall?, lakeInstall?) ← findInstall?
  CliT.run self args {
    shortOption, longOption,
    longShortOption := unknownLongOption,
  } |>.run' {leanInstall?, lakeInstall?}

end CliM

def cli (args : List String) : IO UInt32 :=
  CliM.processArgs.run args
