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

/-- Unsafe implementation of `load`. -/
unsafe def loadUnsafe (dir : FilePath) (args : List String := [])
(configFile := dir / defaultConfigFile) (leanOpts := Options.empty)
: IO Package := do
  let input ← IO.FS.readFile configFile
  let (env, ok) ← Elab.runFrontend input leanOpts configFile.toString configModName
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
