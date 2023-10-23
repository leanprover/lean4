/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Frontend
import Lake.DSL.Extensions
import Lake.Load.Config
import Lake.Build.Trace
import Lake.Util.Log

namespace Lake
open Lean System

deriving instance BEq, Hashable for Import

/- Cache for the imported header environment of Lake configuration files. -/
initialize importEnvCache : IO.Ref (HashMap (Array Import) Environment) ← IO.mkRef {}

/-- Like `importModules`, but fetch the resulting import state from the cache if possible. -/
def importModulesUsingCache (imports : Array Import) (opts : Options) (trustLevel : UInt32) : IO Environment := do
  if let some env := (← importEnvCache.get).find? imports then
    return env
  let env ← importModules imports opts trustLevel
  importEnvCache.modify (·.insert imports env)
  return env

/-- Like `Lean.Elab.processHeader`, but using `importEnvCache`. -/
def processHeader (header : Syntax) (opts : Options)
(inputCtx : Parser.InputContext) : StateT MessageLog IO Environment := do
  try
    let imports := Elab.headerToImports header
    importModulesUsingCache imports opts 1024
  catch e =>
    let pos := inputCtx.fileMap.toPosition <| header.getPos?.getD 0
    modify (·.add { fileName := inputCtx.fileName, data := toString e, pos })
    mkEmptyEnvironment

/-- Main module `Name` of a Lake configuration file. -/
def configModuleName : Name := `lakefile

/-- Elaborate `configFile` with the given package directory and options. -/
def elabConfigFile (pkgDir : FilePath) (lakeOpts : NameMap String)
(leanOpts := Options.empty) (configFile := pkgDir / defaultConfigFile) : LogIO Environment := do

  -- Read file and initialize environment
  let input ← IO.FS.readFile configFile
  let inputCtx := Parser.mkInputContext input configFile.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header leanOpts inputCtx messages
  let env := env.setMainModule configModuleName

  -- Configure extensions
  let env := dirExt.setState env pkgDir
  let env := optsExt.setState env lakeOpts

  -- Elaborate File
  let commandState := Elab.Command.mkState env messages leanOpts
  let s ← Elab.IO.processCommands inputCtx parserState commandState

  -- Log messages
  for msg in s.commandState.messages.toList do
    match msg.severity with
    | MessageSeverity.information => logInfo (← msg.toString)
    | MessageSeverity.warning     => logWarning (← msg.toString)
    | MessageSeverity.error       => logError (← msg.toString)

  -- Check result
  if s.commandState.messages.hasErrors then
    error s!"{configFile}: package configuration has errors"
  else
    return s.commandState.env

/--
`Lean.Environment.add` is now private, but exported as `lean_environment_add`.
We call it here via `@[extern]` with a mock implementation.
-/
@[extern "lean_environment_add"]
private def add (env : Environment) (_ : ConstantInfo) : Environment := env

/--
Import the OLean for the configuration file if `reconfigure` is not set
and an up-to-date one exists (i.e., one newer than the configuration and the
toolchain). Otherwise, elaborate the configuration and save it to the OLean.
-/
def importConfigFile (wsDir pkgDir : FilePath) (lakeOpts : NameMap String)
(leanOpts := Options.empty) (configFile := pkgDir / defaultConfigFile) (reconfigure := true) : LogIO Environment := do
  let olean := configFile.withExtension "olean"
  let useOLean ← id do
    if reconfigure then return false
    let .ok oleanMTime ← getMTime olean |>.toBaseIO | return false
    unless oleanMTime > (← getMTime configFile) do return false
    let toolchainFile := wsDir / toolchainFileName
    let .ok toolchainMTime ← getMTime toolchainFile |>.toBaseIO | return true
    return oleanMTime > toolchainMTime
  if useOLean then
    /- We could import the olean together with its imports using one
       `importModules` call, but that would mean we pay for a full
       `finalizeImports` each time, which is linear in the number of imported
       constants and extension entries (in fact, it is paid two more times: when
       marking the `Environment` object as multi-threaded, and when releasing
       it). As most lakefiles use the same set of imports, we instead construct
       an `Environment` for it only once, and then apply the lakefile contents
       on top of it like the elaborator would. Thus the non-shared, part of the
       `Environment` is very small. -/
    let (mod, _) ← readModuleData olean
    let mut env ← importModulesUsingCache mod.imports leanOpts 1024
    -- Apply constants (does not go through the kernel, so order is irrelevant)
    env := mod.constants.foldl add env
    -- Apply extension entries (`PersistentEnvExtension.addEntryFn` is pure and
    -- does not have access to the whole environment, so no dependency worries
    -- here either)
    let extDescrs ← persistentEnvExtensionsRef.get
    let extNameIdx ← mkExtNameMap 0
    for (extName, ents) in mod.entries do
      if let some entryIdx := extNameIdx.find? extName then
        for ent in ents do
          env := extDescrs[entryIdx]!.addEntry env ent
    return env
  else
    let env ← elabConfigFile pkgDir lakeOpts leanOpts configFile
    Lean.writeModule env olean
    return env
