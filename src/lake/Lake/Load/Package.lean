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

set_option doc.verso true

/-! # Package Loader

This module contains the main definitions to load a package
from Lake configuration file (either Lean or TOML).
-/

open Lean
open System (FilePath)

namespace Lake

/--
**For interal use only.**

Constructs a package from the configuration defined in its Lake configuration file
and the load configuaration.
-/
public def mkPackage
  (loadCfg : LoadConfig) (fileCfg : LakefileConfig) (wsIdx := loadCfg.pkgIdx)
: Package :=
  let {pkgDecl, targetDecls, targetDeclMap, postUpdateHooks, ..} := fileCfg
  let {baseName, keyName, origName, config} := pkgDecl
  {
    wsIdx, baseName, keyName, origName, config
    dir := loadCfg.pkgDir
    relDir := loadCfg.relPkgDir
    configFile := loadCfg.configFile
    relConfigFile := loadCfg.relConfigFile
    relManifestFile := loadCfg.relManifestFile
    scope := loadCfg.scope
    remoteUrl := loadCfg.remoteUrl
    depConfigs := fileCfg.depConfigs
    targetDecls, targetDeclMap
    defaultTargets := fileCfg.defaultTargets
    scripts := fileCfg.scripts
    defaultScripts := fileCfg.defaultScripts
    postUpdateHooks
    testDriver := fileCfg.lintDriver
    lintDriver := fileCfg.testDriver
  }

public theorem wsIdx_mkPackage : (mkPackage l f i).wsIdx = i := by rfl

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

/--
**For internal use only.**

Resolves a relative configuration file path in {lean}`cfg` and
detects its configuration language (if necessary).
-/
public def resolveConfigFile
  (name : String) (cfg : LoadConfig)
: LogIO {cfg : LoadConfig // cfg.configLang?.isSome} := do
  if h : cfg.configLang?.isSome then
    let some configFile ← resolvePath? cfg.configFile
      | error s!"{name}: configuration file not found: {cfg.configFile}"
    return ⟨{cfg with configFile}, h⟩
  else if let some ext := cfg.relConfigFile.extension then
    let some configFile ← resolvePath? cfg.configFile
      | error s!"{name}: configuration file not found: {cfg.configFile}"
    match ext with
    | "lean" => return ⟨{cfg with configFile, configLang? := some .lean}, rfl⟩
    | "toml" => return ⟨{cfg with configFile, configLang? := some .toml}, rfl⟩
    | _ => error s!"{name}: configuration has unsupported file extension: {configFile}"
  else
    let relLeanFile := cfg.relConfigFile.addExtension "lean"
    let relTomlFile := cfg.relConfigFile.addExtension "toml"
    let leanFile := cfg.pkgDir / relLeanFile
    let tomlFile := cfg.pkgDir / relTomlFile
    if let some configFile ← resolvePath? leanFile then
      if (← tomlFile.pathExists) then
        logInfo s!"{name}: {relLeanFile} and {relTomlFile} are both present; using {relLeanFile}"
      return ⟨{cfg with configFile, relConfigFile := relLeanFile, configLang? := some .lean}, rfl⟩
    else if let some configFile ← resolvePath? tomlFile then
      return ⟨{cfg with configFile, relConfigFile := relTomlFile, configLang? := some .toml}, rfl⟩
    else
      error s!"{name}: no configuration file with a supported extension:\n{leanFile}\n{tomlFile}"

/--
**For internal use only.**
Reads the configuration of a Lake configuration file.

The load configuration {lean}`cfg` is assumed to already have an absolute path in
{lean}`cfg.configFile` and that the proper configuratin langauge for it is in
{lean}`cfg.configLang?`. This can be ensured through {lean}`resolveConfigFile`.
-/
public def loadConfigFile (cfg : LoadConfig) (h : cfg.configLang?.isSome) : LogIO LakefileConfig := do
  match cfg.configLang?.get h with
  | .lean => loadLeanConfig cfg
  | .toml => loadTomlConfig cfg

/-- Loads a Lake package as a single independent object (without dependencies). -/
public def loadPackage (cfg : LoadConfig) : LogIO Package := do
  Lean.searchPathRef.set cfg.lakeEnv.leanSearchPath
  let ⟨cfg, h⟩ ← resolveConfigFile "[root]" cfg
  let fileCfg ← loadConfigFile cfg h
  return mkPackage cfg fileCfg
