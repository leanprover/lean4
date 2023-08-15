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

/-! # Loading a Workspace
The main definitions for loading a workspace and resolving dependencies.
-/

namespace Lake

/-- Load the tagged `Dependency` definitions from a package configuration environment. -/
def loadDepsFromEnv (env : Environment) (opts : Options) : Except String (Array Dependency) := do
  (packageDepAttr.ext.getState env).mapM (evalConstCheck env opts Dependency ``Dependency)

/--
Elaborate a dependency's configuration file into a `Package`.
The resulting package does not yet include any dependencies.
-/
def loadDepPackage (wsDir : FilePath) (dep : MaterializedDep)
(leanOpts : Options) (lakeOpts : NameMap String) : LogIO Package := do
  let dir := wsDir / dep.relPkgDir
  let configEnv ← elabConfigFile dir lakeOpts leanOpts (dir / defaultConfigFile)
  let config ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv leanOpts
  return {
    dir, config, configEnv, leanOpts
    remoteUrl? := dep.remoteUrl?
    gitTag? := dep.gitTag?
  }

/--
Rebuild the workspace's Lake manifest and materialize missing dependencies.

Packages are updated to latest specific revision matching that in `require`
(e.g., if the `require` is `@master`, update to latest commit on master) or
removed if the `require` is removed. If `tuUpdate` is empty, update/remove all
root dependencies. Otherwise, only update the root dependencies specified.
-/
def buildUpdatedManifest (ws : Workspace) (toUpdate : NameSet := {}) : LogIO Manifest := do
  let res ← StateT.run (s := mkNameMap MaterializedDep) <| EStateT.run' (mkNameMap Package) do
    -- Use manifest versions of root packages that should not be updated
    unless toUpdate.isEmpty do
      for entry in (← Manifest.loadOrEmpty ws.manifestFile) do
        unless entry.inherited || toUpdate.contains entry.name do
          let dep ← entry.materialize ws.dir ws.relPkgsDir
          modifyThe (NameMap MaterializedDep) (·.insert entry.name dep)
    buildAcyclic (·.1.name) (ws.root, FilePath.mk ".") fun (pkg, relPkgDir) resolve => do
      let inherited := pkg.name != ws.root.name
      let deps ← IO.ofExcept <| loadDepsFromEnv pkg.configEnv pkg.leanOpts
      -- Materialize this package's dependencies first
      let deps ← deps.mapM fun dep => fetchOrCreate dep.name do
        dep.materialize inherited ws.dir ws.relPkgsDir relPkgDir
      -- Load dependency packages and materialize their locked dependencies
      let deps ← deps.mapM fun dep => do
        if let .some pkg := (← getThe (NameMap Package)).find? dep.name then
          return (pkg, dep.relPkgDir)
        else
          -- Load the package
          let depPkg ← loadDepPackage ws.dir dep pkg.leanOpts dep.opts
          if depPkg.name ≠ dep.name then
            logWarning s!"{pkg.name}: package '{depPkg.name}' was required as '{dep.name}'"
          -- Materialize locked dependencies
          for entry in (← Manifest.loadOrEmpty depPkg.manifestFile) do
            unless (← getThe (NameMap MaterializedDep)).contains entry.name do
              let entry := entry.setInherited.inDirectory dep.relPkgDir
              let dep ← entry.materialize ws.dir ws.relPkgsDir
              modifyThe (NameMap MaterializedDep) (·.insert entry.name dep)
          modifyThe (NameMap Package) (·.insert dep.name depPkg)
          return (depPkg, dep.relPkgDir)
      -- Resolve dependencies's dependencies recursively
      return {pkg with opaqueDeps := ← deps.mapM (.mk <$> resolve ·)}
  match res with
  | (.ok _, deps) =>
    let manifest : Manifest := {packagesDir? := ws.relPkgsDir}
    return deps.fold (fun m _ d => m.insert d.manifestEntry) manifest
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
      "manifest out of date: packages directory changed, " ++
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
              s!"manifest out of date: {what} of dependency '{dep.name}' changed, " ++
              "use `lake update` to update"
          if let .some entry := manifest.find? dep.name then
          match dep.src, entry with
          | .git (url := url) (rev := rev) .., .git (url := url') (inputRev? := rev')  .. =>
            if url ≠ url' then warnOutOfDate "git url"
            if rev ≠ rev' then warnOutOfDate "git revision"
          | .path .., .path .. => pure ()
          | _, _ => warnOutOfDate "source kind (git/path)"
      let depPkgs ← deps.mapM fun dep => fetchOrCreate dep.name do
        let .some entry := manifest.find? dep.name
          | error <| s!"dependency '{dep.name}' of '{pkg.name}' not in manifest, " ++
            "use `lake update` to update"
        let result ← entry.materialize ws.dir relPkgsDir
        loadDepPackage ws.dir result pkg.leanOpts dep.opts
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

/-- Updates the manifest for the loaded Lake workspace (see `buildUpdatedManifest`). -/
def updateManifest (config : LoadConfig) (toUpdate : NameSet := {}) : LogIO Unit := do
  let ws ← loadWorkspaceRoot config
  let manifest ← buildUpdatedManifest ws toUpdate
  manifest.saveToFile ws.manifestFile
