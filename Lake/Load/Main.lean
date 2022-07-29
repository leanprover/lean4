/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.EStateT
import Lake.Util.StoreInsts
import Lake.Config.Workspace
import Lake.Build.Topological
import Lake.Build.Module
import Lake.Build.Package
import Lake.Build.Library
import Lake.Load.Materialize
import Lake.Load.Package
import Lake.Load.Elab

open System Lean

namespace Lake

/-- Load the tagged `Dependency` definitions from a package configuration environment. -/
def loadDeps (env : Environment) (opts : Options) : Except String (Array Dependency) := do
  packageDepAttr.ext.getState env |>.foldM (init := #[]) fun arr name => do
    return arr.push <| ← evalConstCheck env opts Dependency ``Dependency name

/--
Resolves the package's dependencies,
downloading and/or updating them as necessary.
-/
def resolveDeps (ws : Workspace) (pkg : Package) (leanOpts : Options)
(deps : Array Dependency) (shouldUpdate := true) : ManifestM (Workspace × Array Package) := do
  have : MonadStore Name Package (StateT Workspace ManifestM) := {
    fetch? := fun name => return (← get).findPackage? name
    store := fun _ pkg => modify (·.addPackage pkg)
  }
  let (res, ws) ← EStateT.run ws <| deps.mapM fun dep =>
    buildTop (·.2.name) (pkg, dep) recResolveDep
  match res with
  | Except.ok deps => return (ws, deps)
  | Except.error cycle => do
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"
where
  recResolveDep info resolve := do
    let ⟨pkg, dep⟩ := info
    let (dir, url?, tag?) ← materializeDep ws.packagesDir pkg.dir dep shouldUpdate
    let configEnv ← elabConfigFile dir dep.options leanOpts (dir / defaultConfigFile)
    let config ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv leanOpts
    let depPkg : Package := {
      dir, config, configEnv, leanOpts
      remoteUrl? := url?, gitTag? := tag?
    }
    unless depPkg.name = dep.name do
      error <|
        s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
        s!"but resolved dependency has name {depPkg.name} (in {dir})"
    let depDeps ← IO.ofExcept <| loadDeps depPkg.configEnv leanOpts
    let depDepPkgs ← depDeps.mapM fun dep => resolve (depPkg, dep)
    set (← IO.ofExcept <| (← get).addFacetsFromEnv depPkg.configEnv depPkg.leanOpts)
    let depPkg ← depPkg.finalize depDepPkgs
    return depPkg

/--
Load a `Workspace` for a Lake package by
elaborating its configuration file and resolve its dependencies.
-/
def loadWorkspace (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.env.leanSearchPath
  let configEnv ← elabConfigFile config.rootDir config.configOpts config.leanOpts config.configFile
  let pkgConfig ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv config.leanOpts
  let repo := GitRepo.mk config.rootDir
  let root : Package := {
    configEnv, leanOpts := config.leanOpts
    dir := config.rootDir, config := pkgConfig
    remoteUrl? := ← repo.getFilteredRemoteUrl?
    gitTag? := ← repo.findTag?
  }
  let ws : Workspace := {
    root, lakeEnv := config.env
    moduleFacetConfigs := initModuleFacetConfigs
    packageFacetConfigs := initPackageFacetConfigs
    libraryFacetConfigs := initLibraryFacetConfigs
  }
  let deps ← IO.ofExcept <| loadDeps root.configEnv config.leanOpts
  let manifest ← Manifest.loadFromFile ws.manifestFile |>.catchExceptions fun _ => pure {}
  let ((ws, deps), manifest) ← resolveDeps ws root
    config.leanOpts deps config.updateDeps |>.run manifest
  unless manifest.isEmpty do
    manifest.saveToFile ws.manifestFile
  let ws ← IO.ofExcept <| ws.addFacetsFromEnv root.configEnv root.leanOpts
  let root ← root.finalize deps
  let packageMap := ws.packageMap.insert root.name root
  return {ws with root, packageMap}
