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

def Package.run (script : String) (args : List String) (self : Package) : IO PUnit :=
  if let some script := self.scripts.find? script then
    script args
  else
    self.scripts.forM fun name _ => IO.println name

-- Hack since Lean provides no methods to remove directories
def removeDirAll (path : System.FilePath) : IO PUnit := do
  runBuild <| Lake.proc {cmd := "rm", args := #["-rf", path.toString]}

def Package.clean (self : Package) : IO PUnit :=
  removeDirAll self.buildDir

-- # CLI

structure CliOptions where
  wantsHelp : Bool := false
  dir : FilePath := "."
  file : FilePath := pkgFileName
  subArgs : List String := []

abbrev CliM := CliT (StateT CliOptions IO)
-- abbrev LakeCliMethods := CliMethods (StateT CliState IO)

namespace CliM
open CliT

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

def getPkg (args : List String) : CliM Package := do
  let pkg ← Package.fromDir (← getDir) args (← getFile)
  if pkg.leanVersion ≠ leanVersionString then
    IO.eprintln $ "\nWARNING: Lean version mismatch: installed version is " ++
      leanVersionString ++ ", but package requires " ++ pkg.leanVersion ++ "\n"
  return pkg

def takeArg : CliM String := do
  match (← takeArg?) with
  | none => throw <| IO.userError "missing argument"
  | some arg => arg

def takeFileArg : CliM FilePath := do
  match (← takeArg?) with
  | none => throw <| IO.userError "missing file argument"
  | some arg => arg

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

def command : (cmd : String) → CliM PUnit
| "new"         => do new (← takeArg)
| "init"        => do init (← takeArg)
| "run"         => do (← getPkg []).run (← takeArg) (← getSubArgs)
| "configure"   => do configure (← getPkg (← getSubArgs))
| "print-paths" => do printPaths (← getPkg (← getSubArgs)) (← takeArgs)
| "build"       => do build (← getPkg (← getSubArgs))
| "build-lib"   => do buildLib (← getPkg (← getSubArgs))
| "build-bin"   => do buildBin (← getPkg (← getSubArgs))
| "clean"       => do (← getPkg (← getSubArgs)).clean
| "help"        => do IO.println <| help (← takeArg?)
| "self-check"  => verifyLeanVersion
| cmd           => throw <| IO.userError s!"unknown command '{cmd}'"

def processArgs : CliM PUnit := do
  match (← getArgs) with
  | [] => throw <| IO.userError "expected command"
  | ["--version"] => IO.println uiVersionString
  | _ => -- normal CLI
    processOptions
    match (← takeArg?) with
    | none =>
      if (← getWantsHelp) then IO.println usage else
      throw <| IO.userError "expected command"
    | some cmd =>
      if (← getWantsHelp) then IO.println (help cmd) else
      command cmd

def run (self : CliM PUnit) (args : List String) : IO PUnit :=
  CliT.run self args {shortOption, longOption, longShortOption := unknownLongOption} |>.run' {}

end CliM

def cli (args : List String) : IO PUnit :=
  CliM.processArgs.run args
