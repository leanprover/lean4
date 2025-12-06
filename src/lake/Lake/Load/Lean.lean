/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lean.Environment
public import Lake.Config.Package
public import Lake.Load.Config
import Lake.Load.Lean.Elab
import Lake.Load.Lean.Eval

/-! # Lean Loader

This module contains the main definitions to load a package from a
Lake configuration file written in Lake's Lean DSL.
-/

open Lean

namespace Lake

/--
Elaborate a Lean configuration file into a `Package`.
The resulting package does not yet include any dependencies.
-/
public def loadLeanConfig (cfg : LoadConfig) : LogIO (Package × Environment) := do
  let configEnv ← importConfigFile cfg
  let ⟨keyName, origName, config⟩ ← IO.ofExcept <| PackageDecl.loadFromEnv configEnv cfg.leanOpts
  let baseName := if cfg.pkgName.isAnonymous then origName else cfg.pkgName
  let pkg : Package := {
    wsIdx := cfg.pkgIdx
    baseName, keyName, origName, config
    dir := cfg.pkgDir
    relDir := cfg.relPkgDir
    configFile := cfg.configFile
    relConfigFile := cfg.relConfigFile
    scope := cfg.scope
    remoteUrl := cfg.remoteUrl
  }
  return (← pkg.loadFromEnv configEnv cfg.leanOpts, configEnv)
