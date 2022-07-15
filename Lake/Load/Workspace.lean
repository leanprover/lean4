/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Load.Resolve

open System
open Lean (Json toJson fromJson?)

namespace Lake

def loadPkg (config : LoadConfig) : LogIO Package := do
  Lean.searchPathRef.set config.env.leanSearchPath
  Package.load config.rootDir config.options config.configFile

def loadManifestMap (manifestFile : FilePath) : LogIO (Lean.NameMap PackageEntry) := do
  if let Except.ok contents ← IO.FS.readFile manifestFile  |>.toBaseIO then
    match Json.parse contents with
    | Except.ok json =>
      match fromJson? json with
      | Except.ok (manifest : Manifest) =>
        return manifest.toMap
      | Except.error e =>
        logWarning s!"improperly formatted package manifest: {e}"
        return {}
    | Except.error e =>
      logWarning s!"invalid JSON in package manifest: {e}"
      return {}
  else
    return {}

def loadWorkspace (config : LoadConfig) (updateDeps := false) : LogIO Workspace := do
  let root ← loadPkg config
  let ws : Workspace := {root, env := config.env}
  let manifestMap ← loadManifestMap ws.manifestFile
  let (packageMap, resolvedMap) ← resolveDeps ws root updateDeps |>.run manifestMap
  unless resolvedMap.isEmpty do
    let json := Json.pretty <| toJson <| Manifest.fromMap resolvedMap
    IO.FS.writeFile ws.manifestFile <| json.push '\n'
  let packageMap := packageMap.insert root.name root
  return {ws with packageMap}
