/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Load.Config
public import Lake.Config.Package
public import Lake.Config.LakefileConfig
import Lake.Util.IO
import Lake.Load.Lean
import Lake.Load.Toml

/-! # Package Loader

This module contains the main definitions to load a package
from Lake configuration file (either Lean or TOML).
-/

open Lean
open System (FilePath)

namespace Lake

/--
**For interal use only.**
Constructo a package from the configuration defined in its Lake configuration file
and the load configuaration.
-/
public def mkPackage (loadCfg : LoadConfig) (fileCfg : LakefileConfig) : Package :=
  let wsIdx := loadCfg.pkgIdx
  let {pkgDecl, targetDecls, targetDeclMap, postUpdateHooks, ..} := fileCfg
  let {baseName, keyName, origName, config} := pkgDecl
  {
    wsIdx, baseName, keyName, origName, config
    dir := loadCfg.pkgDir
    relDir := loadCfg.relPkgDir
    configFile := loadCfg.configFile
    relConfigFile := loadCfg.relConfigFile
    scope := loadCfg.scope
    remoteUrl := loadCfg.remoteUrl
    depConfigs := fileCfg.depConfigs
    targetDecls := targetDecls
    targetDeclMap := targetDeclMap
    defaultTargets := fileCfg.defaultTargets
    scripts := fileCfg.scripts
    defaultScripts := fileCfg.defaultScripts
    postUpdateHooks := postUpdateHooks
    testDriver := fileCfg.lintDriver
    lintDriver := fileCfg.testDriver
  }

public theorem wsIdx_mkPackage : (mkPackage l f).wsIdx = l.pkgIdx := by rfl

/--
Return whether a configuration file with the given name
and/or a supported extension exists.
-/
public def configFileExists (cfgFile : FilePath) : BaseIO Bool :=
  if cfgFile.extension.isSome then
    cfgFile.pathExists
  else
    let leanFile := cfgFile.addExtension "lean"
    let tomlFile := cfgFile.addExtension "toml"
    leanFile.pathExists <||> tomlFile.pathExists

/--
Returns the normalized real path of the configuration file (if it exists).
Otherwise, returns an empty string.
-/
public def realConfigFile (cfgFile : FilePath) : BaseIO FilePath := do
  if cfgFile.extension.isSome then
    resolvePath cfgFile
  else
    if let some path ← resolvePath? (cfgFile.addExtension "lean") then
      return path
    else
      resolvePath (cfgFile.addExtension "toml")

/-- **For internal use only.** Loads a Lake configuration (either Lean or TOML). -/
public def loadConfig
  (name : String) (cfg : LoadConfig)
: LogIO LakefileConfig := do
  if let some ext := cfg.relConfigFile.extension then
    let configFile ←
      if let some configFile ← resolvePath? cfg.configFile then
        pure configFile
      else error s!"{name}: configuration file not found: {cfg.configFile}"
    let cfg := {cfg with configFile}
    match ext with
    | "lean" => loadLeanConfig cfg
    | "toml" => loadTomlConfig cfg
    | _ => error s!"{name}: configuration has unsupported file extension: {cfg.configFile}"
  else
    let relLeanFile := cfg.relConfigFile.addExtension "lean"
    let relTomlFile := cfg.relConfigFile.addExtension "toml"
    let leanFile := cfg.pkgDir / relLeanFile
    let tomlFile := cfg.pkgDir / relTomlFile
    if let some configFile ← resolvePath? leanFile then
      if (← tomlFile.pathExists) then
        logInfo s!"{name}: {relLeanFile} and {relTomlFile} are both present; using {relLeanFile}"
      loadLeanConfig {cfg with configFile, relConfigFile := relLeanFile}
    else
      if let some configFile ← resolvePath? tomlFile then
        loadTomlConfig {cfg with configFile, relConfigFile := relTomlFile}
      else
        error s!"{name}: no configuration file with a supported extension:\n{leanFile}\n{tomlFile}"

/--
**For internal use only.**
Loads a Lake package configuration (either Lean or TOML).
The resulting package does not yet include any dependencies.
-/
@[inline] public def loadPackageCore
  (name : String) (cfg : LoadConfig)
: LogIO {pkg : Package // pkg.wsIdx = cfg.pkgIdx} := do
  let fileCfg ← loadConfig name cfg
  let pkg := mkPackage cfg fileCfg
  return ⟨pkg, wsIdx_mkPackage⟩

/-- Loads a Lake package as a single independent object (without dependencies). -/
public def loadPackage (cfg : LoadConfig) : LogIO Package := do
  Lean.searchPathRef.set cfg.lakeEnv.leanSearchPath
  let fileCfg ← loadConfig "[root]" cfg
  return mkPackage cfg fileCfg
