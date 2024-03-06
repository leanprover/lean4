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

/--
Elaborate a dependency's configuration file into a `Package`.
The resulting package does not yet include any dependencies.
Adds the facets defined in the package to the `Workspace`.
-/
protected def Workspace.loadPackage
  (ws : Workspace) (dep : MaterializedDep)
  (leanOpts : Options) (reconfigure : Bool)
: LogIO (Package × Workspace) := do
  let dir := ws.dir / dep.relPkgDir
  let lakeDir := dir / defaultLakeDir
  let configEnv ← importConfigFile dir lakeDir ws.lakeEnv dep.configOpts leanOpts (dir / dep.configFile) reconfigure
  let config ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv leanOpts
  let pkg : Package := {
    dir
    relDir := dep.relPkgDir
    config
    configFile := dep.configFile
    remoteUrl? := dep.remoteUrl?
  }
  return (
    ← pkg.loadFromEnv configEnv leanOpts,
    ← IO.ofExcept <| ws.addFacetsFromEnv configEnv leanOpts
  )

@[inherit_doc Workspace.loadPackage, inline] def loadPackage
  (dep : MaterializedDep) (leanOpts : Options) (reconfigure : Bool)
: StateT Workspace LogIO Package := fun ws => do
  ws.loadPackage dep leanOpts reconfigure

/--
Load a `Workspace` for a Lake package by elaborating its configuration file.
Does not resolve dependencies.
-/
def loadWorkspaceRoot (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.env.leanSearchPath
  let configEnv ← importConfigFile
    config.rootDir (config.rootDir / defaultLakeDir) config.env
    config.configOpts config.leanOpts config.configFile config.reconfigure
  let pkgConfig ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv config.leanOpts
  let root : Package := {
    dir := config.rootDir
    relDir := "."
    config := pkgConfig
    configFile := config.configFile
  }
  let root ← root.loadFromEnv configEnv config.leanOpts
  let ws : Workspace := {
    root, lakeEnv := config.env
    moduleFacetConfigs := initModuleFacetConfigs
    packageFacetConfigs := initPackageFacetConfigs
    libraryFacetConfigs := initLibraryFacetConfigs
  }
  IO.ofExcept <| ws.addFacetsFromEnv configEnv config.leanOpts

/-- Recursively visits a package dependency graph, avoiding cycles. -/
private def resolveDepsAcyclic
  [Monad m] [MonadError m]
  (root : Package) (f : RecFetchFn Package α (CycleT Name m))
: m α := do
  match (← ExceptT.run <| recFetchAcyclic (·.name) f root []) with
  | .ok s => pure s
  | .error cycle =>
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"

/--
Rebuild the workspace's Lake manifest and materialize missing dependencies.

Packages are updated to latest specific revision matching that in `require`
(e.g., if the `require` is `@master`, update to latest commit on master) or
removed if the `require` is removed. If `tuUpdate` is empty, update/remove all
root dependencies. Otherwise, only update the root dependencies specified.

If `reconfigure`, elaborate configuration files while updating, do not use OLeans.
-/
def Workspace.updateAndMaterialize
  (ws : Workspace) (leanOpts : Options := {})
  (toUpdate : NameSet := {}) (reconfigure := true)
: LogIO Workspace := do
  let ((root, deps), ws) ←
    StateT.run (s := ws) <| StateT.run (s := mkNameMap MaterializedDep) <|
    StateT.run' (s := mkNameMap PackageEntry) <| StateT.run' (s := mkNameMap Package) do
    -- Use manifest versions of root packages that should not be updated
    match (← Manifest.load ws.manifestFile |>.toBaseIO) with
    | .ok manifest =>
      unless toUpdate.isEmpty do
        manifest.packages.forM fun entry => do
          unless entry.inherited || toUpdate.contains entry.name do
            modifyThe (NameMap PackageEntry) (·.insert entry.name entry)
      if let some oldRelPkgsDir := manifest.packagesDir? then
        let oldPkgsDir := ws.dir / oldRelPkgsDir
        if oldPkgsDir != ws.pkgsDir && (← oldPkgsDir.pathExists) then
          let doRename : IO Unit := do
            createParentDirs ws.pkgsDir
            IO.FS.rename oldPkgsDir ws.pkgsDir
          if let .error e ← doRename.toBaseIO then
            error <|
              s!"{ws.root.name}: could not rename packages directory " ++
              s!"({oldPkgsDir} -> {ws.pkgsDir}): {e}"
    | .error (.noFileOrDirectory ..) =>
      logInfo s!"{ws.root.name}: no previous manifest, creating one from scratch"
    | .error e =>
      unless toUpdate.isEmpty do
        liftM (m := IO) <| throw e -- only ignore manifest on a bare `lake update`
      logWarning s!"{ws.root.name}: ignoring previous manifest because it failed to load: {e}"
    resolveDepsAcyclic ws.root fun pkg resolve => do
      let inherited := pkg.name != ws.root.name
      -- Materialize this package's dependencies first
      let deps ← pkg.depConfigs.mapM fun dep => fetchOrCreate dep.name do
        if let some entry := (← getThe (NameMap PackageEntry)).find? dep.name then
          entry.materialize dep ws.dir ws.relPkgsDir ws.lakeEnv.pkgUrlMap
        else
          dep.materialize inherited ws.dir ws.relPkgsDir pkg.relDir ws.lakeEnv.pkgUrlMap
      -- Load dependency packages and materialize their locked dependencies
      let deps ← deps.mapM fun dep => do
        if let some pkg := (← getThe (NameMap Package)).find? dep.name then
          return pkg
        else
          -- Load the package
          let depPkg ← liftM <| loadPackage dep leanOpts reconfigure
          if depPkg.name ≠ dep.name then
            logWarning s!"{pkg.name}: package '{depPkg.name}' was required as '{dep.name}'"
          -- Materialize locked dependencies
          match (← Manifest.load depPkg.manifestFile |>.toBaseIO) with
          | .ok manifest =>
            manifest.packages.forM fun entry => do
              unless (← getThe (NameMap PackageEntry)).contains entry.name do
                let entry := entry.setInherited.inDirectory dep.relPkgDir
                modifyThe (NameMap PackageEntry) (·.insert entry.name entry)
          | .error (.noFileOrDirectory ..) =>
            logWarning s!"{depPkg.name}: ignoring missing dependency manifest '{depPkg.manifestFile}'"
          | .error e =>
            logWarning s!"{depPkg.name}: ignoring dependency manifest because it failed to load: {e}"
          modifyThe (NameMap Package) (·.insert dep.name depPkg)
          return depPkg
      -- Resolve dependencies's dependencies recursively
      let pkg := {pkg with opaqueDeps := ← deps.mapM (.mk <$> resolve ·)}
      modifyThe Workspace (·.addPackage pkg)
      return pkg
  let ws : Workspace := {ws with root}
  let manifest : Manifest := {
    name := ws.root.name
    lakeDir := ws.relLakeDir
    packagesDir? := ws.relPkgsDir
  }
  let manifest := ws.packages.foldl (init := manifest) fun manifest pkg =>
    match deps.find? pkg.name with
    | some dep => manifest.addPackage <|
      dep.manifestEntry.setManifestFile pkg.relManifestFile
    | none => manifest -- should only be the case for the root
  manifest.saveToFile ws.manifestFile
  LakeT.run ⟨ws⟩ <| ws.packages.forM fun pkg => do
    unless pkg.postUpdateHooks.isEmpty do
      logInfo s!"{pkg.name}: running post-update hooks"
      pkg.postUpdateHooks.forM fun hook => hook.get.fn pkg
  return ws

/--
Resolving a workspace's dependencies using a manifest,
downloading and/or updating them as necessary.
-/
def Workspace.materializeDeps
  (ws : Workspace) (manifest : Manifest)
  (leanOpts : Options := {}) (reconfigure := false)
: LogIO Workspace := do
  if !manifest.packages.isEmpty && manifest.packagesDir? != some (normalizePath ws.relPkgsDir) then
    logWarning <|
      "manifest out of date: packages directory changed; " ++
      "use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)"
  let relPkgsDir := manifest.packagesDir?.getD ws.relPkgsDir
  let pkgEntries := manifest.packages.foldl (init := mkNameMap PackageEntry)
    fun map entry => map.insert entry.name entry
  let rootPkg := ws.root
  let (root, ws) ← StateT.run (s := ws) <| StateT.run' (s := mkNameMap Package) do
    resolveDepsAcyclic rootPkg fun pkg resolve => do
      let topLevel := pkg.name = rootPkg.name
      let deps := pkg.depConfigs
      if topLevel then
        if manifest.packages.isEmpty && !deps.isEmpty then
          error "missing manifest; use `lake update` to generate one"
        for dep in deps do
          let warnOutOfDate (what : String) :=
            logWarning <|
              s!"manifest out of date: {what} of dependency '{dep.name}' changed; " ++
              s!"use `lake update {dep.name}` to update it"
          if let .some entry := pkgEntries.find? dep.name then
          match dep.src, entry with
          | .git (url := url) (rev := rev) .., .git (url := url') (inputRev? := rev')  .. =>
            if url ≠ url' then warnOutOfDate "git url"
            if rev ≠ rev' then warnOutOfDate "git revision"
          | .path .., .path .. => pure ()
          | _, _ => warnOutOfDate "source kind (git/path)"
      let depPkgs ← deps.mapM fun dep => fetchOrCreate dep.name do
        if let some entry := pkgEntries.find? dep.name then
          let ws ← getThe Workspace
          let result ← entry.materialize dep ws.dir relPkgsDir ws.lakeEnv.pkgUrlMap
          liftM <| loadPackage result leanOpts reconfigure
        else if topLevel then
          error <|
            s!"dependency '{dep.name}' not in manifest; " ++
            s!"use `lake update {dep.name}` to add it"
        else
          error <|
            s!"dependency '{dep.name}' of '{pkg.name}' not in manifest; " ++
            "this suggests that the manifest is corrupt;" ++
            "use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)"
      let pkg := {pkg with opaqueDeps := ← depPkgs.mapM (.mk <$> resolve ·)}
      modifyThe Workspace (·.addPackage pkg)
      return pkg
  return {ws with root}

/--
Load a `Workspace` for a Lake package by
elaborating its configuration file and resolving its dependencies.
If `updateDeps` is true, updates the manifest before resolving dependencies.
-/
def loadWorkspace (config : LoadConfig) (updateDeps := false) : LogIO Workspace := do
  let rc := config.reconfigure
  let leanOpts := config.leanOpts
  let ws ← loadWorkspaceRoot config
  if updateDeps then
    ws.updateAndMaterialize leanOpts {} rc
  else if let some manifest ← Manifest.load? ws.manifestFile then
    ws.materializeDeps manifest leanOpts rc
  else
    ws.updateAndMaterialize leanOpts {} rc

/-- Updates the manifest for the loaded Lake workspace (see `updateAndMaterialize`). -/
def updateManifest (config : LoadConfig) (toUpdate : NameSet := {}) : LogIO Unit := do
  let rc := config.reconfigure
  let leanOpts := config.leanOpts
  let ws ← loadWorkspaceRoot config
  discard <| ws.updateAndMaterialize leanOpts toUpdate rc
