/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
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
def loadLeanConfig (cfg : LoadConfig)
: LogIO (Package × Environment) := do
  let configEnv ← importConfigFile cfg
  let {name, config} ← IO.ofExcept <| PackageDecl.loadFromEnv configEnv cfg.leanOpts
  let pkg : Package := {
    name, config
    dir := cfg.pkgDir
    relDir := cfg.relPkgDir
    configFile := cfg.configFile
    relConfigFile := cfg.relConfigFile
    scope := cfg.scope
    remoteUrl := cfg.remoteUrl
  }
  return (← pkg.loadFromEnv configEnv cfg.leanOpts, configEnv)
