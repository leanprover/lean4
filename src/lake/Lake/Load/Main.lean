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
import Lake.Load.Toml

open System Lean

/-! # Loading a Workspace
The main definitions for loading a workspace and resolving dependencies.
-/

namespace Lake

/--
Elaborate a dependency's Lean configuration file into a `Package`.
The resulting package does not yet include any dependencies.
-/
def loadLeanConfig (cfg : LoadConfig)
: LogIO (Package × Environment) := do
  let configEnv ← importConfigFile cfg
  let pkgConfig ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv cfg.leanOpts
  let pkg : Package := {
    dir := cfg.pkgDir
    relDir := cfg.relPkgDir
    config := pkgConfig
    relConfigFile := cfg.relConfigFile
    remoteUrl? := cfg.remoteUrl?
  }
  return (← pkg.loadFromEnv configEnv cfg.leanOpts, configEnv)

/--
Return whether a configuration file with the given name
and/or a supported extension exists.
-/
def configFileExists (cfgFile : FilePath) : BaseIO Bool :=
  if cfgFile.extension.isSome then
    cfgFile.pathExists
  else
    let leanFile := cfgFile.addExtension "lean"
    let tomlFile := cfgFile.addExtension "toml"
    leanFile.pathExists <||> tomlFile.pathExists

/-- Loads a Lake package configuration (either Lean or TOML). -/
def loadPackage
  (name : String) (cfg : LoadConfig)
: LogIO (Package × Option Environment) := do
  if let some ext := cfg.relConfigFile.extension then
    unless (← cfg.configFile.pathExists) do
      error s!"{name}: configuration file not found: {cfg.configFile}"
    match ext with
    | "lean" => (·.map id some) <$> loadLeanConfig cfg
    | "toml" => ((·,none)) <$> loadTomlConfig cfg.pkgDir cfg.relPkgDir cfg.relConfigFile
    | _ => error s!"{name}: configuration has unsupported file extension: {cfg.configFile}"
  else
    let relLeanFile := cfg.relConfigFile.addExtension "lean"
    let relTomlFile := cfg.relConfigFile.addExtension "toml"
    let leanFile := cfg.pkgDir / relLeanFile
    let tomlFile := cfg.pkgDir / relTomlFile
    let leanExists ← leanFile.pathExists
    let tomlExists ← tomlFile.pathExists
    if leanExists then
      if tomlExists then
        logInfo s!"{name}: {relLeanFile} and {relTomlFile} are both present; using {relLeanFile}"
      (·.map id some) <$> loadLeanConfig {cfg with relConfigFile := relLeanFile}
    else
      if tomlExists then
        ((·,none)) <$> loadTomlConfig cfg.pkgDir cfg.relPkgDir relTomlFile
      else
        error s!"{name}: no configuration file with a supported extension:\n{leanFile}\n{tomlFile}"

/-- Construct a load configuration for a materialized dependency. -/
def MaterializedDep.mkLoadConfig
  (lakeEnv : Env) (dep : MaterializedDep)
  (lakeOpts : NameMap String) (leanOpts : Options) (reconfigure : Bool)
: LoadConfig := {
  lakeEnv
  rootDir := dep.rootDir
  relPkgDir := dep.relPkgDir
  relConfigFile := dep.configFile
  lakeOpts, leanOpts, reconfigure
  remoteUrl? := dep.remoteUrl?
}

/--
Loads the package configuration of a materialized dependency.
Adds the facets defined in the package to the `Workspace`.
-/
def loadDepPackage
  (dep : MaterializedDep)
  (lakeOpts : NameMap String) (leanOpts : Options) (reconfigure : Bool)
: StateT Workspace LogIO Package := fun ws => do
  let name := dep.name.toString (escape := false)
  let (pkg, env?) ← loadPackage name <|
    dep.mkLoadConfig ws.lakeEnv lakeOpts leanOpts reconfigure
  if let some env := env? then
    let ws ← IO.ofExcept <| ws.addFacetsFromEnv env leanOpts
    return (pkg, ws)
  else
    return (pkg, ws)

/--
Load a `Workspace` for a Lake package by elaborating its configuration file.
Does not resolve dependencies.
-/
def loadWorkspaceRoot (config : LoadConfig) : LogIO Workspace := do
  Lean.searchPathRef.set config.lakeEnv.leanSearchPath
  let (root, env?) ← loadPackage "[root]" config
  let ws : Workspace := {
    root, lakeEnv := config.lakeEnv
    moduleFacetConfigs := initModuleFacetConfigs
    packageFacetConfigs := initPackageFacetConfigs
    libraryFacetConfigs := initLibraryFacetConfigs
  }
  if let some env := env? then
    IO.ofExcept <| ws.addFacetsFromEnv env config.leanOpts
  else
    return ws

@[inline] private def failOnDepCycle
  [Monad m] [MonadError m] (r : ExceptT (Cycle Name) m α)
: m α := do
  match (← ExceptT.run r) with
  | .ok a => pure a
  | .error cycle =>
    let cycle := cycle.map (s!"  {·}")
    error s!"dependency cycle detected:\n{"\n".intercalate cycle}"

/--
Recursively visits the workspace dependency graph, starting from `root`.
At each package, performs `f` to resolve the dependencies of a package,
recurses, then adds the package to workspace's package set.
Errors if a cycle is encountered.
-/
@[inline] private def Workspace.resolveDeps
  [Monad m] [MonadError m]
  (ws : Workspace) (f : Package → StateT Workspace m (Array Package))
: m Workspace := do
  let (root, ws) ← StateT.run (s := ws) <|
    failOnDepCycle <| recFetchAcyclic (·.name) go ws.root []
  return {ws with root}
where
  @[specialize] go pkg resolve := do
    if let some pkg := (← getThe Workspace).findPackage? pkg.name then
        return pkg
    let deps ← liftM <| f pkg
    let deps ← deps.mapM fun dep => return OpaquePackage.mk (← resolve dep)
    let pkg := {pkg with opaqueDeps := deps}
    modifyThe Workspace (·.addPackage pkg)
    return pkg

/-- Load a JSON array of installed packages. -/
def loadInstallEntries (pkgsFile : FilePath) : LogIO (Array PackageEntry) := do
  match (← IO.FS.readFile pkgsFile |>.toBaseIO) with
  | .ok contents =>
    match Json.parse contents >>= fromJson? with
    | .ok entries => return entries
    | .error e =>
      error s!"toolchain package list has invalid JSON: {e}; \
        to fix this, you may need to reinstall the toolchain"
  | .error (.noFileOrDirectory ..) =>
    return #[]
  | .error e =>
    error s!"could not read toolchain package list: {e}"

/-- Load installed packages into the workspace. -/
def Workspace.loadInstalledDeps
  (ws : Workspace) (leanOpts : Options := {})
: LogIO Workspace := Prod.snd <$> StateT.run (s := ws) do
  match (← ws.lakeEnv.getToolchainDir.toBaseIO) with
  | .ok toolchainDir =>
    let pkgsDir := toolchainDir / installedPackagesDir
    let entries ← loadInstallEntries (toolchainDir / installedPackagesFile)
    let pkgEntries : NameMap PackageEntry := entries.foldl (init := {})
      fun map entry => map.insert entry.name entry
    let go entry resolve : CycleT Name (StateT Workspace LogIO) Package := do
      let ws ← getThe Workspace
      if let some pkg := ws.findPackage? entry.name then
        return pkg
      let matDep ← entry.materialize ws.lakeEnv pkgsDir "."
      let pkg ← loadDepPackage matDep {} leanOpts false
      let deps ← pkg.depConfigs.mapM fun dep => do
        let some entry := pkgEntries.find? dep.name
          | error s!"dependency '{dep.name}' not install manifest; \
            this should never happen and that Lake's install configuration is corrupt; \
            please file a bug report about this issue"
        return .mk (← resolve entry)
      let pkg := {pkg with opaqueDeps := deps}
      modifyThe Workspace (·.addPackage pkg)
      return pkg
    failOnDepCycle <| entries.forM fun e => unless e.inherited do
       discard <| recFetchAcyclic (·.name) go e []
  | .error e =>
    logInfo s!"no installed packages; could not locate Elan toolchain directory: {e}"

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
  let ws ← ws.loadInstalledDeps leanOpts
  let startIdx := ws.packages.size
  let (ws, entries) ← StateT.run (s := mkNameMap PackageEntry) do
    -- Use manifest versions of root packages that should not be updated
    match (← Manifest.load ws.manifestFile |>.toBaseIO) with
    | .ok manifest =>
      unless toUpdate.isEmpty do
        manifest.packages.forM fun entry => do
          unless entry.inherited || toUpdate.contains entry.name do
            modifyThe (NameMap PackageEntry) (·.insert entry.name entry)
      if let some oldRelPkgsDir := manifest.packagesDir? then
        let oldPkgsDir := ws.dir / oldRelPkgsDir
        if oldRelPkgsDir.normalize != ws.relPkgsDir.normalize && (← oldPkgsDir.pathExists) then
          logInfo s!"workspace packages directory changed; \
            renaming '{oldPkgsDir}' to '{ws.pkgsDir}'"
          let doRename : IO Unit := do
            createParentDirs ws.pkgsDir
            IO.FS.rename oldPkgsDir ws.pkgsDir
          if let .error e ← doRename.toBaseIO then
            error s!"could not rename workspace packages directory: {e}"
    | .error (.noFileOrDirectory ..) =>
      logInfo s!"{ws.root.name}: no previous manifest, creating one from scratch"
    | .error e =>
      unless toUpdate.isEmpty do
        liftM (m := IO) <| throw e -- only ignore manifest on a bare `lake update`
      logWarning s!"{ws.root.name}: ignoring previous manifest because it failed to load: {e}"
    -- Resolve dependencies
    ws.resolveDeps fun pkg => do
      let inherited := pkg.name != (← getThe Workspace).root.name
      -- Verify there are not multiple dependencies with the same name in the package
      discard <| pkg.depConfigs.foldlM (init := NameSet.empty) fun set dep => do
        if set.contains dep.name then
          error "{pkg.name}: duplicate require of package '{dep.name}'"
        else
          return set.insert dep.name
      -- Materialize and load this package's dependencies first
      let deps ← pkg.depConfigs.mapM fun dep => do
        let matDep ←
          if let some entry := (← getThe (NameMap PackageEntry)).find? dep.name then
            entry.materialize ws.lakeEnv ws.dir ws.relPkgsDir
          else
            dep.materialize inherited ws.lakeEnv ws.dir ws.relPkgsDir pkg.relDir
        -- Load the package
        let depPkg ← liftM <| loadDepPackage matDep dep.opts leanOpts reconfigure
        if depPkg.name ≠ dep.name then
          error s!"{pkg.name}: package '{depPkg.name}' was required as '{dep.name}'"
        return depPkg
      -- Add the dependencies' locked dependencies to the manifest
      let deps ← deps.mapM fun dep => do
        match (← Manifest.load dep.manifestFile |>.toBaseIO) with
        | .ok manifest =>
          manifest.packages.forM fun entry => do
            unless (← getThe (NameMap PackageEntry)).contains entry.name do
              let entry := entry.setInherited.inDirectory dep.relDir
              modifyThe (NameMap PackageEntry) (·.insert entry.name entry)
        | .error (.noFileOrDirectory ..) =>
          logWarning s!"{dep.name}: ignoring missing dependency manifest '{dep.manifestFile}'"
        | .error e =>
          logWarning s!"{dep.name}: ignoring dependency manifest because it failed to load: {e}"
        return dep
      -- Resolve dependencies's dependencies recursively
      return deps
  let manifest : Manifest := {
    name := ws.root.name
    lakeDir := ws.relLakeDir
    packagesDir? := ws.relPkgsDir
  }
  let manifest := ws.packages.foldl (start := startIdx) (init := manifest) fun manifest pkg =>
    match entries.find? pkg.name with
    | some entry => manifest.addPackage <|
      entry.setManifestFile pkg.relManifestFile |>.setConfigFile pkg.relConfigFile
    | none => manifest -- should only be the case for the root
  manifest.saveToFile ws.manifestFile
  LakeT.run ⟨ws⟩ <| ws.packages.forM (start := startIdx) fun pkg => do
    unless pkg.postUpdateHooks.isEmpty do
      logInfo s!"{pkg.name}: running post-update hooks"
      pkg.postUpdateHooks.forM fun hook => hook.get.fn pkg
  return ws

/--
Check whether the manifest exists and
whether entries in the manifest are up-to-date,
reporting warnings and/or errors as appropriate.
-/
def validateManifest
  (pkgEntries : NameMap PackageEntry) (deps : Array Dependency)
: LogIO PUnit := do
  if pkgEntries.isEmpty && !deps.isEmpty then
    error "missing manifest; use `lake update` to generate one"
  deps.forM fun dep => do
    let warnOutOfDate (what : String) :=
      logWarning <|
        s!"manifest out of date: {what} of dependency '{dep.name}' changed; \
        use `lake update {dep.name}` to update it"
    if let .some entry := pkgEntries.find? dep.name then
    match dep.src, entry with
    | .git (url := url) (rev := rev) .., .git (url := url') (inputRev? := rev')  .. =>
      if url ≠ url' then warnOutOfDate "git url"
      if rev ≠ rev' then warnOutOfDate "git revision"
    | .path .., .path .. => pure ()
    | _, _ => warnOutOfDate "source kind (git/path)"

/--
Resolving a workspace's dependencies using a manifest,
downloading and/or updating them as necessary.
-/
def Workspace.materializeDeps
  (ws : Workspace) (manifest : Manifest)
  (leanOpts : Options := {}) (reconfigure := false)
: LogIO Workspace := do
  if !manifest.packages.isEmpty && manifest.packagesDir? != some (mkRelPathString ws.relPkgsDir) then
    logWarning <|
      "manifest out of date: packages directory changed; \
      use `lake update` to rebuild the manifest \
      (warning: this will update ALL workspace dependencies)"
  let relPkgsDir := manifest.packagesDir?.getD ws.relPkgsDir
  let pkgEntries : NameMap PackageEntry := manifest.packages.foldl (init := {})
    fun map entry => map.insert entry.name entry
  validateManifest pkgEntries ws.root.depConfigs
  let ws ← ws.loadInstalledDeps leanOpts
  let ws ← ws.resolveDeps fun pkg => pkg.depConfigs.mapM fun dep => do
    let ws ← getThe Workspace
    if let some entry := pkgEntries.find? dep.name then
      let result ← liftM <| entry.materialize ws.lakeEnv ws.dir relPkgsDir
      liftM <| loadDepPackage result dep.opts leanOpts reconfigure
    else
      if pkg.name = ws.root.name then
        error <|
          s!"dependency '{dep.name}' not in manifest; \
          use `lake update {dep.name}` to add it"
      else
        error <|
          s!"dependency '{dep.name}' of '{pkg.name}' not in manifest; \
          this suggests that the manifest is corrupt; \
          use `lake update` to generate a new, complete file \
          (warning: this will update ALL workspace dependencies)"
  return ws

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
