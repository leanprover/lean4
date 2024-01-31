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

/-- Load the tagged `PackageDepConfig` definitions from a package configuration environment. -/
def loadDepsFromEnv (env : Environment) (opts : Options) : Except String (Array PackageDepConfig) := do
  (packageDepAttr.getAllEntries env).mapM (evalConstCheck env opts PackageDepConfig ``PackageDepConfig)

/--
Elaborate a dependency's configuration file into a `Package`.
The resulting package does not yet include any dependencies.
-/
def MaterializedDep.loadPackage (dep : MaterializedDep)
(wsDir : FilePath) (leanOpts : Options) (reconfigure : Bool) : LogIO Package := do
  let dir := wsDir / dep.relPkgDir
  let lakeDir := dir / defaultLakeDir
  let configEnv ← importConfigFile dir lakeDir dep.configOpts leanOpts (dir / dep.configFile) reconfigure
  let config ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv leanOpts
  return {
    dir
    relDir := dep.relPkgDir
    config, configEnv, leanOpts
    configFile := dep.configFile
    remoteUrl? := dep.remoteUrl?
  }

/--
Load a `Workspace` for a Lake package by elaborating its configuration file.
Does not resolve dependencies.
-/
def loadWorkspaceRoot (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.env.leanSearchPath
  let configEnv ← importConfigFile
    config.rootDir (config.rootDir / defaultLakeDir)
    config.configOpts config.leanOpts config.configFile config.reconfigure
  let pkgConfig ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv config.leanOpts
  let root := {
    dir := config.rootDir
    relDir := "."
    config := pkgConfig
    configEnv
    leanOpts := config.leanOpts
    configFile := config.configFile
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
  have : MonadStore SimpleName Package (StateT Workspace LogIO) := {
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

structure UpdateState where
  pkgs : SimpleNameMap Package := {}
  mdeps : SimpleNameMap MaterializedDep := {}
  entries : SimpleNameMap PackageEntry := {}

abbrev UpdateT := EStateT (Cycle Name) UpdateState
@[inline] def UpdateT.run [Functor m] (x : UpdateT m α) : m (Except (Cycle Name) α × UpdateState)  :=
  EStateT.run {} x
@[inline] def addEntry [Monad m] [MonadStateOf UpdateState m] (entry : PackageEntry) : m PUnit :=
   modify fun s => {s with entries := s.entries.insert entry.name entry}

/--
Rebuild the workspace's Lake manifest and materialize missing dependencies.

Packages are updated to latest specific revision matching that in `require`
(e.g., if the `require` is `@master`, update to latest commit on master) or
removed if the `require` is removed. If `tuUpdate` is empty, update/remove all
root dependencies. Otherwise, only update the root dependencies specified.

If `reconfigure`, elaborate configuration files while updating, do not use OLeans.
-/
def Workspace.updateAndMaterialize (ws : Workspace)
(toUpdate : SimpleNameSet := {}) (reconfigure := true) : LogIO Workspace := do
  let res ← UpdateT.run do
    -- Use manifest versions of root packages that should not be updated
    match (← Manifest.load ws.manifestFile |>.toBaseIO) with
    | .ok manifest =>
      unless toUpdate.isEmpty do
        manifest.packages.forM fun entry => do
          unless entry.inherited || toUpdate.contains entry.name do
            addEntry entry
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
    buildAcyclic (·.name) ws.root fun pkg resolve => do
      let inherited := pkg.name != ws.root.name
      -- Materialize this package's dependencies first
      let deps ← IO.ofExcept <| loadDepsFromEnv pkg.configEnv pkg.leanOpts
      let deps ← deps.mapM fun dep => do
        if let some dep := (← get).mdeps.find? dep.name then
          return dep
        else
          let dep ←
            if let some entry := (← get).entries.find? dep.name then
              entry.materialize dep ws.dir ws.relPkgsDir ws.lakeEnv
            else
              dep.materialize inherited ws.dir ws.relPkgsDir pkg.relDir ws.lakeEnv
          modify fun s => {s with mdeps := s.mdeps.insert dep.name dep}
          return dep
      -- Load dependency packages and materialize their locked dependencies
      let deps ← deps.mapM fun dep => do
        if let some pkg := (← get).pkgs.find? dep.name then
          return pkg
        else
          -- Load the package
          let depPkg ← dep.loadPackage ws.dir pkg.leanOpts reconfigure
          if depPkg.name ≠ dep.name then
            error s!"{pkg.name}: package '{depPkg.name}' was required as '{dep.name}'"
          -- Materialize locked dependencies
          match (← Manifest.load depPkg.manifestFile |>.toBaseIO) with
          | .ok manifest =>
            manifest.packages.forM fun entry => do
              unless (← get).entries.contains entry.name do
                addEntry <| entry.setInherited.inDirectory dep.relPkgDir
          | .error (.noFileOrDirectory ..) =>
            logWarning s!"{depPkg.name}: ignoring missing dependency manifest '{depPkg.manifestFile}'"
          | .error e =>
            logWarning s!"{depPkg.name}: ignoring dependency manifest because it failed to load: {e}"
          modify fun s => {s with pkgs := s.pkgs.insert dep.name depPkg}
          return depPkg
      -- Resolve dependencies's dependencies recursively
      return {pkg with opaqueDeps := ← deps.mapM (.mk <$> resolve ·)}
  match res with
  | (.ok root, s) =>
    let ws : Workspace ← {ws with root}.finalize
    let manifest : Manifest := {
      name := ws.root.name
      lakeDir := ws.relLakeDir
      packagesDir? := ws.relPkgsDir
    }
    let manifest := ws.packages.foldl (init := manifest) fun manifest pkg =>
      match s.mdeps.find? pkg.name with
      | some dep => manifest.addPackage <|
        dep.manifestEntry.setManifestFile pkg.relManifestFile
      | none => manifest -- should only be the case for the root
    manifest.saveToFile ws.manifestFile
    LakeT.run ⟨ws⟩ <| ws.packages.forM fun pkg => do
      unless pkg.postUpdateHooks.isEmpty do
        logInfo s!"{pkg.name}: running post-update hooks"
        pkg.postUpdateHooks.forM fun hook => hook.get.fn pkg
    return ws
  | (.error cycle, _) =>
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"

/--
Resolving a workspace's dependencies using a manifest,
downloading and/or updating them as necessary.
-/
def Workspace.materializeDeps (ws : Workspace) (manifest : Manifest) (reconfigure := false) : LogIO Workspace := do
  if !manifest.packages.isEmpty && manifest.packagesDir? != some (normalizePath ws.relPkgsDir) then
    logWarning <|
      "manifest out of date: packages directory changed; " ++
      "use `lake update` to rebuild the manifest (warning: this will update ALL workspace dependencies)"
  let relPkgsDir := manifest.packagesDir?.getD ws.relPkgsDir
  let pkgEntries := manifest.packages.foldl (init := mkNameMap PackageEntry)
    fun map entry => map.insert entry.name entry
  let res ← EStateT.run' (mkSimpleNameMap Package) do
    buildAcyclic (·.name) ws.root fun pkg resolve => do
      let topLevel := pkg.name = ws.root.name
      let deps ← IO.ofExcept <| loadDepsFromEnv pkg.configEnv pkg.leanOpts
      if topLevel then
        if manifest.packages.isEmpty && !deps.isEmpty then
          error "missing manifest; use `lake update` to generate one"
        for dep in deps do
          let warnOutOfDate (what : String) :=
            logWarning <|
              s!"manifest out of date: {what} of dependency '{dep.name}' changed; " ++
              s!"use `lake update {dep.name}` to update it"
          if let .some entry := pkgEntries.find? dep.name then
          match dep.source?, entry.source with
          | some <| .git (url := url) (rev? := rev?) ..,
            .git (url := url') (inputRev? := rev?')  .. =>
            if url ≠ url' then warnOutOfDate "git url"
            if rev? ≠ rev?' then warnOutOfDate "git revision"
          | some <| .github (owner := owner) (repo := repo) (rev? := rev?) ..,
            .github (owner := owner') (repo := repo') (inputRev? := rev?')  .. =>
            if owner ≠ owner' ∨  repo ≠ repo' then warnOutOfDate "github repository"
            if rev? ≠ rev?' then warnOutOfDate "git revision"
          | some <| .path .., .path .. => pure ()
          | none, .registry (inputRev? := rev?) .. =>
            if dep.version? ≠ rev? then warnOutOfDate "git revision"
          | _, _ => warnOutOfDate "source kind (path, git, etc.)"
      let depPkgs ← deps.filterMapM fun dep =>
        if !dep.enable then return none else some <$> fetchOrCreate dep.name do
        if let some entry := pkgEntries.find? dep.name then
          let result ← entry.materialize dep ws.dir relPkgsDir ws.lakeEnv
          result.loadPackage ws.dir pkg.leanOpts reconfigure
        else if topLevel then
          error <|
            s!"dependency '{dep.name}' not in manifest; " ++
            s!"use `lake update {dep.name}` to add it"
        else
          error <|
            s!"dependency '{dep.name}' of '{pkg.name}' not in manifest; " ++
            "this suggests that the manifest is corrupt;" ++
            "use `lake update` to generate a new, complete file (warning: this will update ALL workspace dependencies)"
      return {pkg with opaqueDeps := ← depPkgs.mapM (.mk <$> resolve ·)}
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
  let rc := config.reconfigure
  let ws ← loadWorkspaceRoot config
  if updateDeps then
    ws.updateAndMaterialize {} rc
  else if let some manifest ← Manifest.load? ws.manifestFile then
    ws.materializeDeps manifest rc
  else
    ws.updateAndMaterialize {} rc

/-- Updates the manifest for the loaded Lake workspace (see `updateAndMaterialize`). -/
def updateManifest (config : LoadConfig) (toUpdate : SimpleNameSet := {}) : LogIO Unit := do
  let rc := config.reconfigure
  let ws ← loadWorkspaceRoot config
  discard <| ws.updateAndMaterialize toUpdate rc
