/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lean.Elab.Frontend
import Lake.DSL.Attributes
import Lake.Config.Package

namespace Lake
open Lean System

/-- Main module `Name` of a Lake configuration file. -/
def configModName : Name := `lakefile

/-- The default name of the Lake configuration file (i.e., `lakefile.lean`). -/
def defaultConfigFile : FilePath := "lakefile.lean"

/-- Evaluate a `package` declaration to its respective `PackageConfig`. -/
unsafe def evalPackageDecl (env : Environment) (declName : Name)
(dir : FilePath) (args : List String := []) (leanOpts := Options.empty)
: IO PackageConfig := do
  let m := env.evalConstCheck IOPackager leanOpts ``IOPackager declName
  if let Except.ok ioPackager := m.run.run then
    return ← ioPackager dir args
  let m := env.evalConstCheck Packager leanOpts ``Packager declName
  if let Except.ok packager := m.run.run then
    return packager dir args
  let m := env.evalConstCheck PackageConfig leanOpts ``PackageConfig declName
  if let Except.ok config := m.run.run then
    return config
  error <| s!"unexpected type at `{declName}`, " ++
    "`Lake.IOPackager`, `Lake.Packager`, or `Lake.PackageConfig` expected"

/-- Evaluate a `script` declaration to its respective `Script`. -/
unsafe def evalScriptDecl
(env : Environment) (declName : Name) (leanOpts := Options.empty) : IO Script := do
  let fn ← IO.ofExcept <| Id.run <| ExceptT.run <|
    env.evalConstCheck ScriptFn leanOpts ``ScriptFn declName
  return {fn, doc? := (← findDocString? env declName)}

namespace Package

deriving instance BEq, Hashable for Import

/- Cache for the imported header environment of Lake configuration files. -/
initialize importEnvCache : IO.Ref (Std.HashMap (List Import) Environment) ← IO.mkRef {}

/-- Like `Lean.Elab.processHeader`, but using `importEnvCache`. -/
def processHeader (header : Syntax) (messages : MessageLog) (inputCtx : Parser.InputContext) (trustLevel : UInt32)
: IO (Environment × MessageLog) := do
  try
    let imports := Elab.headerToImports header
    if let some env := (← importEnvCache.get).find? imports then return (env, messages)
    let env ← importModules imports {} trustLevel
    importEnvCache.modify (·.insert imports env)
    return (env, messages)
  catch e =>
    let env ← mkEmptyEnvironment
    let spos := header.getPos?.getD 0
    let pos  := inputCtx.fileMap.toPosition spos
    return (env, messages.add { fileName := inputCtx.fileName, data := toString e, pos })

/-- Like `Lean.Elab.runFrontend`, but using `importEnvCache`. -/
def runFrontend (input : String) (opts : Options) (fileName : String) (mainModuleName : Name) (trustLevel : UInt32 := 1024)
: IO (Environment × Bool) := do
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header messages inputCtx trustLevel
  let env := env.setMainModule mainModuleName

  let mut commandState := Elab.Command.mkState env {} opts
  let s ← Elab.IO.processCommands inputCtx parserState commandState
  for msg in s.commandState.messages.toList do
    IO.eprint (← msg.toString)

  pure (s.commandState.env, !s.commandState.messages.hasErrors)

/-- Unsafe implementation of `load`. -/
unsafe def loadUnsafe (dir : FilePath) (args : List String := [])
(configFile := dir / defaultConfigFile) (leanOpts := Options.empty)
: IO Package := do
  let input ← IO.FS.readFile configFile
  let (env, ok) ← runFrontend input leanOpts configFile.toString configModName
  if ok then
    match packageAttr.ext.getState env |>.toList with
    | [] => error s!"configuration file is missing a `package` declaration"
    | [pkgDeclName] =>
      let config ← evalPackageDecl env pkgDeclName dir args leanOpts
      let scripts ← scriptAttr.ext.getState env |>.foldM (init := {})
        fun m d => return m.insert d <| ← evalScriptDecl env d leanOpts
      return {dir, config, scripts}
    | _ => error s!"configuration file has multiple `package` declarations"
  else
    error s!"package configuration `{configFile}` has errors"

/--
Load the package located in
the given directory with the given configuration file.
-/
@[implementedBy loadUnsafe]
constant load (dir : FilePath) (args : List String := [])
(configFile := dir / defaultConfigFile) (leanOpts := Options.empty) : IO Package
