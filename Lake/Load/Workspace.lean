/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load.Resolve

namespace Lake

def loadWorkspace (config : LoadConfig) (updateDeps := false) : LogIO Workspace := do
  Lean.searchPathRef.set config.env.leanSearchPath
  let root ← Package.load config.rootDir config.options config.configFile
  let ws : Workspace := {root, env := config.env}
  let manifest ← Manifest.loadFromFile ws.manifestFile |>.catchExceptions fun _ => pure {}
  let (packageMap, manifest) ← resolveDeps ws root updateDeps |>.run manifest
  unless manifest.isEmpty do
    manifest.saveToFile ws.manifestFile
  let packageMap := packageMap.insert root.name root
  return {ws with packageMap}
