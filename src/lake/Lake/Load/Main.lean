/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
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
def loadDepsFromEnv (env : Environment) (opts : Options) : Except String (Array Dependency) := do
  (packageDepAttr.ext.getState env).mapM (evalConstCheck env opts Dependency ``Dependency)

def loadDepPackage (parentPkg : Package) (result : MaterializeResult)
(dep : Dependency) : LogIO Package := do
  let dir := result.pkgDir
  let configEnv ← elabConfigFile dir dep.options parentPkg.leanOpts (dir / defaultConfigFile)
  let config ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv parentPkg.leanOpts
  return {
    dir, config, configEnv
    remoteUrl? := result.remoteUrl?
    gitTag? := result.gitTag?
    leanOpts := parentPkg.leanOpts
  }

def buildUpdatedManifest (ws : Workspace) : LogIO Manifest := do
  let res ← StateT.run (s := mkNameMap MaterializeResult) do
    EStateT.run' (mkNameMap Package) do
      buildAcyclic (·.name) ws.root fun pkg resolve => do
        let topLevel := pkg.name = ws.root.name
        let relPkgDir :=
          if let some {relPkgDir, ..} := ((← getThe (NameMap MaterializeResult)).find? pkg.name) then
            relPkgDir
          else
            "." -- topLevel
        unless topLevel do
          for entry in (← Manifest.loadOrEmpty pkg.manifestFile) do
            unless (← getThe (NameMap MaterializeResult)).contains entry.name do
              let entry := entry.inDirectory relPkgDir
              let result ← materializePackageEntry ws.dir ws.relPkgsDir entry
              modifyThe (NameMap MaterializeResult) (·.insert entry.name result)
        let deps ← IO.ofExcept <| loadDepsFromEnv pkg.configEnv pkg.leanOpts
        let deps ← deps.mapM fun dep => do
          if let some result := (← getThe (NameMap MaterializeResult)).find? dep.name then
            return (dep, result)
          else
            let depName := dep.name.toString (escape := false)
            let entry ← updateSource relPkgDir ws.relPkgsDir depName dep.src
            let result ← materializePackageEntry ws.dir ws.relPkgsDir entry
            modifyThe (NameMap MaterializeResult) (·.insert entry.name result)
            return (dep, result)
        let depPkgs ← deps.mapM fun (dep, result) => do
          if let .some pkg := (← getThe (NameMap Package)).find? dep.name then
            return pkg
          else
            let pkg ← loadDepPackage pkg result dep
            modifyThe (NameMap Package) (·.insert dep.name pkg)
            return pkg
        return {pkg with opaqueDeps := ← depPkgs.mapM (.mk <$> resolve ·)}
  match res with
  | (.ok _, results) =>
    let mut manifest : Manifest := {packagesDir? := ws.relPkgsDir}
    for (_, result) in results do
      manifest := manifest.insert result.manifestEntry
    return manifest
  | (.error cycle, _) =>
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"

/--
Load a `Workspace` for a Lake package by elaborating its configuration file.
Does not resolve dependencies.
-/
def loadWorkspaceRoot (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.env.leanSearchPath
  let configEnv ← elabConfigFile config.rootDir config.configOpts config.leanOpts config.configFile
  let pkgConfig ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv config.leanOpts
  let repo := GitRepo.mk config.rootDir
  let root := {
    configEnv, leanOpts := config.leanOpts
    dir := config.rootDir, config := pkgConfig
    remoteUrl? := ← repo.getFilteredRemoteUrl?
    gitTag? := ← repo.findTag?
  }
  return {
    root, lakeEnv := config.env
    moduleFacetConfigs := initModuleFacetConfigs
    packageFacetConfigs := initPackageFacetConfigs
    libraryFacetConfigs := initLibraryFacetConfigs
  }

/--
Finalize the workspace's root and its transitive dependencies
and add them to the workspace.
-/
def Workspace.finalize (ws : Workspace) : LogIO Workspace := do
  have : MonadStore Name Package (StateT Workspace LogIO) := {
    fetch? := fun name => return (← get).findPackage? name
    store := fun _ pkg => modify (·.addPackage pkg)
  }
  let (res, ws) ← EStateT.run ws do
    buildTop (·.name) ws.root fun pkg load => do
      let depPkgs ← pkg.deps.mapM load
      set <| ← IO.ofExcept <| (← get).addFacetsFromEnv pkg.configEnv pkg.leanOpts
      let pkg ← pkg.finalize depPkgs
      return pkg
  match res with
  | Except.ok root =>
    return {ws with root}
  | Except.error cycle => do
    let cycle := cycle.map (s!"  {·}")
    error <|
      s!"oops! dependency load cycle detected (this likely indicates a bug in Lake):\n" ++
      "\n".intercalate cycle

/--
Resolving a workspace's dependencies using a manifest,
downloading and/or updating them as necessary.
-/
def Workspace.materializeDeps (ws : Workspace) (manifest : Manifest) : LogIO Workspace := do
  if !manifest.isEmpty && manifest.packagesDir? != some ws.relPkgsDir then
    logWarning <|
      "manifest out of date: package directory changed, " ++
      "use `lake update` to update"
  let relPkgsDir := manifest.packagesDir?.getD ws.relPkgsDir
  let res ← EStateT.run' (mkNameMap Package) do
    buildAcyclic (·.name) ws.root fun pkg resolve => do
      let topLevel := pkg.name = ws.root.name
      let deps ← IO.ofExcept <| loadDepsFromEnv pkg.configEnv pkg.leanOpts
      if topLevel then
        for dep in deps do
          let warnOutOfDate (what : String) :=
            logWarning <|
              s!"manifest out of date: {what} of dependency {dep.name} changed, " ++
              "use `lake update` to update"
          if let .some entry := manifest.find? dep.name then
          match dep.src, entry with
          | .git url rev _, .git _ url' _ rev' _ =>
            if url ≠ url' then warnOutOfDate "git url"
            if rev ≠ rev' then warnOutOfDate "git revision"
          | .path .., .path .. => pure ()
          | _, _ => warnOutOfDate "source kind (git/path)"
      let depPkgs ← deps.mapM fun dep => do
        fetchOrCreate dep.name do
          let .some entry := manifest.find? dep.name
            | error <| s!"dependency {dep.name} of {pkg.name} not in manifest, " ++
              "use `lake update` to update"
          let result ← materializePackageEntry ws.dir relPkgsDir entry
          loadDepPackage pkg result dep
      return { pkg with opaqueDeps := ← depPkgs.mapM (.mk <$> resolve ·) }
  match res with
  | Except.ok root =>
    ({ws with root}).finalize
  | Except.error cycle =>
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"

/--
Load a `Workspace` for a Lake package by
elaborating its configuration file and resolving its dependencies.
If `updateDeps` is true, updates the manifest before resolving dependencies.
-/
def loadWorkspace (config : LoadConfig) (updateDeps := false) : LogIO Workspace := do
  let ws ← loadWorkspaceRoot config
  let manifest ← do
    if updateDeps then
      let manifest ← buildUpdatedManifest ws
      manifest.saveToFile ws.manifestFile
      pure manifest
    else
      Manifest.loadOrEmpty ws.manifestFile
  ws.materializeDeps manifest

/-- Updates the manifest for a Lake package. -/
def updateManifest (config : LoadConfig) : LogIO Unit := do
  let ws ← loadWorkspaceRoot config
  let manifest ← buildUpdatedManifest ws
  manifest.saveToFile ws.manifestFile
