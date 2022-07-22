/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.EStateT
import Lake.Util.StoreInsts
import Lake.Load.Package
import Lake.Load.Materialize
import Lake.Config.Workspace
import Lake.Build.Topological

open System Lean

namespace Lake

/--
Elaborate a package configuration file and
construct a bare `Package` from its `PackageConfig` file.
-/
def loadPkg (dir : FilePath) (configOpts : NameMap String)
(leanOpts := Options.empty) (configFile := dir / defaultConfigFile) : LogIO Package := do
  let configEnv ← elabConfigFile dir configOpts leanOpts configFile
  let config ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv leanOpts
  return {dir, config, configEnv, leanOpts}

/-- Load the tagged `Dependency` definitions from a package configuration environment. -/
def loadDeps (env : Environment) (opts : Options) : Except String (Array Dependency) := do
  packageDepAttr.ext.getState env |>.foldM (init := #[]) fun arr name => do
    return arr.push <| ← evalConstCheck env opts Dependency ``Dependency name

/--
Resolves the package's dependencies,
downloading and/or updating them as necessary.
-/
def resolveDeps (ws : Workspace) (pkg : Package) (leanOpts : Options)
(deps : Array Dependency) (shouldUpdate := true) : ManifestM (Array Package × NameMap Package) := do
  let (res, map) ← EStateT.run (Std.mkRBMap _ _ Name.quickCmp) <| deps.mapM fun dep =>
    buildTop (·.2.name) recResolveDep (pkg, dep)
  match res with
  | Except.ok deps => return (deps, map)
  | Except.error cycle => do
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"
where
  recResolveDep info resolve := do
    let ⟨pkg, dep⟩ := info
    let dir ← materializeDep ws.packagesDir pkg.dir dep shouldUpdate
    let depPkg ← loadPkg dir dep.options leanOpts
    unless depPkg.name = dep.name do
      error <|
        s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
        s!"but resolved dependency has name {depPkg.name} (in {dir})"
    let depDeps ← IO.ofExcept <| loadDeps depPkg.configEnv leanOpts
    let depDepPkgs ← depDeps.mapM fun dep => resolve (depPkg, dep)
    let depPkg ← depPkg.finalize depDepPkgs
    return depPkg

/--
Load a `Workspace` for a Lake package by
elaborating its configuration file and resolve its dependencies.
-/
def loadWorkspace (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.env.leanSearchPath
  let root ← loadPkg config.rootDir config.configOpts config.leanOpts config.configFile
  let ws : Workspace := {root, lakeEnv := config.env}
  let deps ← IO.ofExcept <| loadDeps root.configEnv config.leanOpts
  let manifest ← Manifest.loadFromFile ws.manifestFile |>.catchExceptions fun _ => pure {}
  let ((deps, packageMap), manifest) ← resolveDeps ws root
    config.leanOpts deps config.updateDeps |>.run manifest
  unless manifest.isEmpty do
    manifest.saveToFile ws.manifestFile
  let root ← root.finalize deps
  let packageMap := packageMap.insert root.name root
  return {ws with root, packageMap}
