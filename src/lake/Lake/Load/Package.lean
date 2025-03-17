/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Load.Lean
import Lake.Load.Toml

/-! # Package Loader

This module contains the main definitions to load a package
from Lake configuration file (either Lean or TOML).
-/

open Lean

namespace Lake
open System (FilePath)

/--
Return whether a configuration file with the given name
and/or a supported extension exists.
-/
def configFileExists (cfgFile : FilePath) : BaseIO Bool :=
  if cfgFile.extension.isSome then
    cfgFile.pathExists
  else
    let leanFile := cfgFile.addExtension "lean"
    let tomlFile := cfgFile.addExtension "toml"
    leanFile.pathExists <||> tomlFile.pathExists

/--
Returns the absolute path of the configuration file (if it exists).
Otherwise, returns an empty string.
-/
def realConfigFile (cfgFile : FilePath) : BaseIO FilePath := do
  if cfgFile.extension.isSome then
    realPath cfgFile
  else
    let realLeanFile ← realPath (cfgFile.addExtension "lean")
    if realLeanFile.toString.isEmpty then
      realPath (cfgFile.addExtension "toml")
    else
      return realLeanFile
where
  @[inline] realPath file := do
    match (← (IO.FS.realPath file).toBaseIO) with
    | .ok path => return if (← path.pathExists) then path else ""
    | _ => return ""

/--
Loads a Lake package configuration (either Lean or TOML).
The resulting package does not yet include any dependencies.
-/
def loadPackageCore
  (name : String) (cfg : LoadConfig)
: LogIO (Package × Option Environment) := do
  if let some ext := cfg.relConfigFile.extension then
    unless (← cfg.configFile.pathExists) do
      error s!"{name}: configuration file not found: {cfg.configFile}"
    match ext with
    | "lean" => (·.map id some) <$> loadLeanConfig cfg
    | "toml" => ((·,none)) <$> loadTomlConfig cfg
    | _ => error s!"{name}: configuration has unsupported file extension: {cfg.configFile}"
  else
    let relLeanFile := cfg.relConfigFile.addExtension "lean"
    let relTomlFile := cfg.relConfigFile.addExtension "toml"
    let leanFile := cfg.pkgDir / relLeanFile
    let tomlFile := cfg.pkgDir / relTomlFile
    let leanExists ← leanFile.pathExists
    let tomlExists ← tomlFile.pathExists
    if leanExists then
      if tomlExists then
        logInfo s!"{name}: {relLeanFile} and {relTomlFile} are both present; using {relLeanFile}"
      (·.map id some) <$> loadLeanConfig {cfg with relConfigFile := relLeanFile}
    else
      if tomlExists then
        ((·,none)) <$> loadTomlConfig {cfg with relConfigFile := relTomlFile}
      else
        error s!"{name}: no configuration file with a supported extension:\n{leanFile}\n{tomlFile}"

/-- Loads a Lake package as a single independent object (without dependencies). -/
def loadPackage (config : LoadConfig) : LogIO Package := do
  Lean.searchPathRef.set config.lakeEnv.leanSearchPath
  (·.1) <$> loadPackageCore "[root]" config
