/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Load.Config
public import Lake.Config.Workspace
import Lake.Load.Resolve
import Lake.Load.Package
import Lake.Load.Lean.Eval
import Lake.Build.InitFacets

/-! # Workspace Loader

This module contains the main definitions for loading a complete Lake workspace.
-/

open Lean

namespace Lake

/--
Load a `Workspace` for a Lake package by elaborating its configuration file.
Does not resolve dependencies.
-/
private def loadWorkspaceRoot (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.lakeEnv.leanSearchPath
  let (root, env?) ← loadPackageCore "[root]" {config with pkgIdx := 0}
  let root := {root with outputsRef? := ← CacheRef.mk}
  let ws : Workspace := {
    root
    lakeEnv := config.lakeEnv
    lakeArgs? := config.lakeArgs?
    facetConfigs := initFacetConfigs
  }
  if let some env := env? then
    IO.ofExcept <| ws.addFacetsFromEnv env config.leanOpts
  else
    return ws

/--
Load a `Workspace` for a Lake package by
elaborating its configuration file and resolving its dependencies.
If `updateDeps` is true, updates the manifest before resolving dependencies.
-/
public def loadWorkspace (config : LoadConfig) : LoggerIO Workspace := do
  let {reconfigure, leanOpts, updateDeps, updateToolchain, packageOverrides, ..} := config
  let ws ← loadWorkspaceRoot config
  if updateDeps then
    ws.updateAndMaterialize {} leanOpts updateToolchain
  else if let some manifest ← Manifest.load? ws.manifestFile then
    ws.materializeDeps manifest leanOpts reconfigure packageOverrides
  else
    ws.updateAndMaterialize {} leanOpts updateToolchain

/-- Updates the manifest for the loaded Lake workspace (see `updateAndMaterialize`). -/
public def updateManifest
  (config : LoadConfig) (toUpdate : NameSet := {})
: LoggerIO Unit := do
  let {leanOpts, updateToolchain, ..} := config
  let ws ← loadWorkspaceRoot config
  discard <| ws.updateAndMaterialize toUpdate leanOpts updateToolchain
