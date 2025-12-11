/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Config.Package
public import Lake.Config.LakefileConfig
public import Lake.Load.Config
import Lake.Load.Lean.Elab
import Lake.Load.Lean.Eval

/-! # Lean Loader

This module contains the main definitions to load a package from a
Lake configuration file written in Lake's Lean DSL.
-/

open Lean

namespace Lake

/-- Elaborate a Lake configuration file written in Lean and extract the Lake configuration.  -/
public def loadLeanConfig  (cfg : LoadConfig) : LogIO LakefileConfig := do
  let configEnv ← importConfigFile cfg
  LakefileConfig.loadFromEnv configEnv cfg.leanOpts
