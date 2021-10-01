/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Init
import Lake.Help
import Lake.BuildBin
import Lake.LeanConfig
import Lake.CliT

open System
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
  file : FilePath := defaultConfigFile
  subArgs : List String := []

abbrev CliM := CliT <| StateT CliOptions IO

namespace CliM
open CliT

-- ## State Management

def getDir : CliM FilePath :=
  getThe CliOptions >>= (·.dir)

def setDir (dir : FilePath) : CliM PUnit :=
  modifyThe CliOptions fun st => {st with dir := dir}

def getFile : CliM FilePath :=
  getThe CliOptions >>= (·.file)

def setFile (file : FilePath) : CliM PUnit :=
  modifyThe CliOptions fun st => {st with file := file}

def getSubArgs : CliM (List String) :=
  getThe CliOptions >>= (·.subArgs)

def setSubArgs (args : List String) : CliM PUnit :=
  modifyThe CliOptions fun st => {st with subArgs := args}

def getWantsHelp : CliM Bool :=
  getThe CliOptions >>= (·.wantsHelp)

def setWantsHelp : CliM PUnit :=
  modifyThe CliOptions fun st => {st with wantsHelp := true}

def loadPkg (args : List String) : CliM Package := do
  Package.fromDir (← getDir) args (← getFile)

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
| 'f' => do setFile (← takeFileArg)
| opt => unknownShortOption opt

def unknownLongOption (opt : String) : CliM PUnit :=
  throw <| IO.userError s!"unknown long option '{opt}'"

def longOption : (opt : String) → CliM PUnit
| "--help"  => setWantsHelp
| "--dir"   => do setDir (← takeFileArg)
| "--file"  => do setFile (← takeFileArg)
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

/-- Run the given script from the given package with the given arguments. -/
def script (pkg : Package) (name : String) (args : List String) :  CliM UInt32 := do
  if let some script := pkg.scripts.find? name then
    script args
  else
    pkg.scripts.forM fun name _ => IO.println name
    error s!"unknown script '{name}'"

def command : (cmd : String) → CliM UInt32
| "new"         => do execIO <| new (← takeArg)
| "init"        => do execIO <| init (← takeArg)
| "run"         => do script (← loadPkg []) (← takeArg) (← getSubArgs)
| "configure"   => do execIO <| configure (← loadPkg (← getSubArgs))
| "print-paths" => do execIO <| printPaths (← loadPkg (← getSubArgs)) (← takeArgs)
| "build"       => do execIO <| build (← loadPkg (← getSubArgs))
| "build-lib"   => do execIO <| buildLib (← loadPkg (← getSubArgs))
| "build-bin"   => do execIO <| buildBin (← loadPkg (← getSubArgs))
| "clean"       => do execIO <| (← loadPkg (← getSubArgs)).clean
| "help"        => do output <| help (← takeArg?)
| "self-check"  => execIO verifyLeanVersion
| cmd           => error s!"unknown command '{cmd}'"

def processArgs : CliM UInt32 := do
  match (← getArgs) with
  | [] => output usage
  | ["--version"] => output uiVersionString
  | _ => -- normal CLI
    processOptions
    if let some cmd ← takeArg? then
      if (← getWantsHelp) then output (help cmd) else command cmd
    else
      if (← getWantsHelp) then output usage else error "expected command"

def run (self : CliM α) (args : List String) : IO α :=
  CliT.run self args {
    shortOption, longOption,
    longShortOption := unknownLongOption
  } |>.run' {}

end CliM

def cli (args : List String) : IO UInt32 :=
  CliM.processArgs.run args
