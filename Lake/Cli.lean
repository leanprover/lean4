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
import Lake.MainM
import Lake.CliT

open System
open Lean (Name LeanPaths Json toJson)

namespace Lake

-- # Utilities

def Package.run (script : String) (args : List String) (self : Package) : IO UInt32 :=
  if let some script := self.scripts.find? script then
    script.run args
  else do
    throw <| IO.userError s!"unknown script {script}"

def Package.clean (self : Package) : IO PUnit := do
  if (← self.buildDir.pathExists) then
    IO.FS.removeDirAll self.buildDir

open PackageFacet in
def Package.defaultTarget (self : Package) : OpaqueTarget :=
  match self.defaultFacet with
  | bin => self.binTarget.withoutInfo
  | staticLib => self.staticLibTarget.withoutInfo
  | sharedLib => self.sharedLibTarget.withoutInfo
  | oleans =>  self.oleanTarget.withoutInfo

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
def error (msg : String) (rc : UInt32 := 1) : CliM α := do
  RealM.runIO_ <| IO.eprintln s!"error: {msg}"
  exit rc

/--
  Perform an IO action.
  If it throws an error, invoke `error` with the its message.
-/
def runIO (x : IO α) : CliM α := do
  match (← RealM.runIO' x) with
  | Except.ok a => pure a
  | Except.error e => error (toString e)

instance : MonadLift IO CliM := ⟨runIO⟩

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
def runBuildM (x : BuildM α) : CliM α := do
  let (leanInstall, lakeInstall) ← getInstall
  let leanTrace ← computeTrace leanInstall.lean
  x.run LogMethods.io {leanTrace, leanInstall, lakeInstall}

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
| "--lean"  => do setLean (← takeArg)
| "--"      => do setSubArgs (← takeArgs)
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
    args := #["--version"]
  }
  if out.exitCode == 0 then
    unless out.stdout.drop 14 |>.startsWith uiLeanVersionString do
      error s!"expected {uiLeanVersionString}, but got {out.stdout.trim}"
  else
    error s!"running `lean --version` exited with code {out.exitCode}"

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
    let pkg ← loadPkg (← getSubArgs)
    let leanTrace ← computeTrace leanInstall.lean
    let pkgs ← pkg.buildImportsAndDeps imports |>.run LogMethods.eio {
      leanTrace, leanInstall, lakeInstall
    }
    IO.println <| Json.compress <| toJson {
      oleanPath := pkgs.map (·.oleanDir),
      srcPath := pkgs.map (·.srcDir) : LeanPaths
    }
  else
    exit noConfigFileCode

def resolvePkgSpec (rootPkg : Package) (spec : String) : CliM Package := do
  if spec.isEmpty then
    return rootPkg
  let pkgName := spec.toName
  if pkgName == rootPkg.name then
    return rootPkg
  if let some dep := rootPkg.dependencies.find? (·.name == pkgName) then
    runIO <| LogMethodsT.run LogMethods.io <| resolveDep rootPkg dep
  else
    error s!"unknown package `{spec}`"

def parseTargetBaseSpec (rootPkg : Package) (spec : String) : CliM (Package × Option Name) := do
  match spec.splitOn "/" with
  | [pkgStr] =>
    return (← resolvePkgSpec rootPkg pkgStr, none)
  | [pkgStr, modStr] =>
    let mod := modStr.toName
    let pkg ← resolvePkgSpec rootPkg pkgStr
    if pkg.hasModule mod then
      return (pkg, mod)
    else
      error s!"package '{pkgStr}' has no module '{modStr}'"
  | _ =>
    error s!"invalid target spec '{spec}' (too many '/')"

partial def parseTargetSpec (rootPkg : Package) (spec : String) : CliM OpaqueTarget := do
  match spec.splitOn ":" with
  | [rootSpec] =>
    let (pkg, mod?) ← parseTargetBaseSpec rootPkg rootSpec
    if let some mod := mod? then
      return pkg.moduleOleanTarget mod |>.withoutInfo
    else
      return pkg.defaultTarget
  | [rootSpec, facet] =>
    let (pkg, mod?) ← parseTargetBaseSpec rootPkg rootSpec
    if let some mod := mod? then
      if facet == "olean" then
        return pkg.moduleOleanTarget mod |>.withoutInfo
      else if facet == "c" then
        return pkg.moduleOleanAndCTarget mod |>.withoutInfo
      else if facet == "o" then
        return pkg.moduleOTarget mod |>.withoutInfo
      else
        error s!"unknown module facet '{facet}'"
    else
      if facet == "bin" then
        return pkg.binTarget.withoutInfo
      else if facet == "staticLib" then
        return pkg.staticLibTarget.withoutInfo
      else if facet == "sharedLib" then
        return pkg.sharedLibTarget.withoutInfo
      else if facet == "oleans" then
        return pkg.oleanTarget.withoutInfo
      else
        error s!"unknown package facet '{facet}'"
  | _ =>
    error s!"invalid target spec '{spec}' (too many ':')"

def build (rootPkg : Package) (targetSpecs : List String) : CliM PUnit := do
  let targets ← targetSpecs.mapM (parseTargetSpec rootPkg)
  if targets.isEmpty then
    runBuildM rootPkg.defaultTarget.build
  else
    runBuildM <| targets.forM (·.build)

def server (leanInstall : LeanInstall) (pkg : Package) (args : List String) : CliM PUnit := do
  let child ← IO.Process.spawn {
    cmd := leanInstall.lean.toString,
    args := #["--server"] ++ pkg.moreServerArgs ++ args
  }
  exit (← child.wait)

def command : (cmd : String) → CliM PUnit
| "new"         => do noArgsRem <| new (← takeArg)
| "init"        => do noArgsRem <| init (← takeArg)
| "run"         => do noArgsRem <| script (← loadPkg []) (← takeArg) (← getSubArgs)
| "server"      => do noArgsRem <| server (← getLeanInstall) (← loadPkg []) (← getSubArgs)
| "configure"   => do noArgsRem <| runBuildM (← loadPkg (← getSubArgs)).buildDepOleans
| "print-paths" => do printPaths (← takeArgs)
| "build"       => do build (← loadPkg (← getSubArgs)) (← takeArgs)
| "clean"       => do noArgsRem <| (← loadPkg (← getSubArgs)).clean
| "help"        => do IO.println <| help (← takeArg?)
| "self-check"  => noArgsRem <| verifyInstall
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
        processOptions -- after/intermixed with args
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
