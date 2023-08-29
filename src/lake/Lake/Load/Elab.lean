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

/- Cache for the import state of Lake configuration files. -/
initialize importStateCache : IO.Ref (HashMap (Array Import) ImportState) ← IO.mkRef {}

/--
Like `importModulesCore`, but fetch the
resulting import state from the cache if possible. -/
def importModulesUsingCache (imports : Array Import) : IO ImportState := do
  match (← importStateCache.get).find? imports with
  | none =>
    let (_, s) ← importModulesCore imports |>.run
    importStateCache.modify (·.insert imports s)
    return s
  | some s =>
    return s

/-- Like `Lean.Elab.processHeader`, but using `importEnvCache`. -/
def processHeader (header : Syntax) (opts : Options)
(inputCtx : Parser.InputContext) : StateT MessageLog IO Environment := do
  try
    let imports := Elab.headerToImports header
    withImporting do
      let s ← importModulesUsingCache imports
      finalizeImport s imports opts 1024
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
If `reconfigure` is not set and up-to-date OLean for the configuration file exists,
import it. Otherwise, elaborate the configuration and store save it to the OLean.
-/
def importConfigFile (pkgDir : FilePath) (lakeOpts : NameMap String)
(leanOpts := Options.empty) (configFile := pkgDir / defaultConfigFile) (reconfigure := true) : LogIO Environment := do
  let olean := configFile.withExtension "olean"
  let useOLean ← id do
    if reconfigure then return false
    unless (← olean.pathExists) do return false
    unless (← getMTime olean) > (← getMTime configFile) do return false
    return true
  if useOLean then
    withImporting do
    let (mod, region) ← readModuleData olean
    let s ← importModulesUsingCache mod.imports
    let s := {s with
      moduleData  := s.moduleData.push mod
      regions     := s.regions.push region
      moduleNames := s.moduleNames.push configModuleName
    }
    finalizeImport s #[configModuleName] leanOpts 1024
  else
    let env ← elabConfigFile pkgDir lakeOpts leanOpts configFile
    Lean.writeModule env olean
    return env
