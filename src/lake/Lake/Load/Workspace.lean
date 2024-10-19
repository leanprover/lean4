/-
Copyright (c) 2024 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load.Resolve
import Lake.Build.Module
import Lake.Build.Package
import Lake.Build.Library

/-! # Workspace Loader

This module contains the main definitions for loading a complete Lake workspace.
-/

open Lean

namespace Lake

/--
Load a `Workspace` for a Lake package by elaborating its configuration file.
Does not resolve dependencies.
-/
def loadWorkspaceRoot (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.lakeEnv.leanSearchPath
  let (root, env?) ← loadPackageCore "[root]" config
  let ws : Workspace := {
    root
    lakeEnv := config.lakeEnv
    lakeArgs? := config.lakeArgs?
    moduleFacetConfigs := initModuleFacetConfigs
    packageFacetConfigs := initPackageFacetConfigs
    libraryFacetConfigs := initLibraryFacetConfigs
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
def loadWorkspace (config : LoadConfig) : LoggerIO Workspace := do
  let {reconfigure, leanOpts, updateDeps, updateToolchain, ..} := config
  let ws ← loadWorkspaceRoot config
  if updateDeps then
    ws.updateAndMaterialize {} leanOpts updateToolchain
  else if let some manifest ← Manifest.load? ws.manifestFile then
    ws.materializeDeps manifest leanOpts reconfigure
  else
    ws.updateAndMaterialize {} leanOpts updateToolchain

/-- Updates the manifest for the loaded Lake workspace (see `updateAndMaterialize`). -/
def updateManifest (config : LoadConfig) (toUpdate : NameSet := {})
: LoggerIO Unit := do
  let {leanOpts, updateToolchain, ..} := config
  let ws ← loadWorkspaceRoot config
  discard <| ws.updateAndMaterialize toUpdate leanOpts updateToolchain
