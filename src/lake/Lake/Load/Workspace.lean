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
import Lake.Load.Toml
import Lake.Build.InitFacets

/-! # Workspace Loader

This module contains the main definitions for loading a complete Lake workspace.
-/

open Lean

namespace Lake

/--
**For internal use only.**
Load a `Workspace` for a Lake package by elaborating its configuration file.
Does not resolve dependencies.
-/
public def loadWorkspaceRoot (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.lakeEnv.leanSearchPath
  let lakeConfig ← loadLakeConfig config.lakeEnv
  let config := {config with pkgIdx := 0}
  let ⟨config, h⟩ ← resolveConfigFile "[root]" config
  let fileCfg ← loadConfigFile config h
  let root := mkPackage config fileCfg 0
  have wsIdx_root : root.wsIdx = 0 := wsIdx_mkPackage
  let facetConfigs := fileCfg.facetDecls.foldl (·.insert ·.config) initFacetConfigs
  return {
    lakeEnv := config.lakeEnv
    lakeCache := computeLakeCache root config.lakeEnv
    lakeConfig
    lakeArgs? := config.lakeArgs?
    facetConfigs
    packages := #[root]
    packageMap := DNameMap.empty.insert root.keyName root
    size_packages_pos := by simp
    packages_wsIdx {i} h := by
      cases i with
      | zero => simp [wsIdx_root]
      | succ => simp at h
    depIdxs_packages := by simp [root]
  }

/--
Module name roots owned by the Lean toolchain.

A workspace library providing one of these shadows the toolchain's own modules for every module in
the workspace, because Lake resolves imports against the workspace before the search path. In the
case of `Init` that replaces the prelude implicitly imported by every module, so only packages that
are Lean itself (`bootstrap`) may declare them.
-/
def reservedModuleRoots : Array Name := #[`Init, `Std, `Lean, `Lake]

/-- Errors if a non-`bootstrap` package declares a library rooted at a reserved module name. -/
def Workspace.validateModuleRoots (self : Workspace) : LoggerIO PUnit := do
  for pkg in self.packages do
    if pkg.bootstrap then
      continue
    for lib in pkg.leanLibs do
      for root in lib.roots do
        if reservedModuleRoots.contains root.getRoot then
          error s!"{pkg.prettyName}: library '{lib.name}' is rooted at '{root}', which is reserved \
            for the Lean toolchain"

/--
Load a `Workspace` for a Lake package by
elaborating its configuration file and resolving its dependencies.
If `updateDeps` is true, updates the manifest before resolving dependencies.
-/
public def loadWorkspace (config : LoadConfig) : LoggerIO Workspace := do
  let {reconfigure, leanOpts, updateDeps, updateToolchain, packageOverrides, ..} := config
  let ws ← loadWorkspaceRoot config
  let ws ←
    if updateDeps then
      ws.updateAndMaterialize {} leanOpts updateToolchain
    else if let some manifest ← Manifest.load? ws.manifestFile then
      ws.materializeDeps manifest leanOpts reconfigure packageOverrides
    else
      ws.updateAndMaterialize {} leanOpts updateToolchain
  ws.validateModuleRoots
  return ws

/-- Updates the manifest for the loaded Lake workspace (see `updateAndMaterialize`). -/
public def updateManifest
  (config : LoadConfig) (toUpdate : NameSet := {})
: LoggerIO Unit := do
  let {leanOpts, updateToolchain, ..} := config
  let ws ← loadWorkspaceRoot config
  discard <| ws.updateAndMaterialize toUpdate leanOpts updateToolchain
