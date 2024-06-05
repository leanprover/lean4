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
def loadPackageCore
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

/--
Loads the package configuration of a materialized dependency.
Adds the facets defined in the package to the `Workspace`.
-/
def loadDepPackage
  (dep : MaterializedDep)
  (lakeOpts : NameMap String) (leanOpts : Options) (reconfigure : Bool)
: StateT Workspace LogIO Package := fun ws => do
  let name := dep.name.toString (escape := false)
  let (pkg, env?) ← loadPackageCore name {
    lakeEnv := ws.lakeEnv
    wsDir := ws.dir
    relPkgDir := dep.relPkgDir
    relConfigFile := dep.configFile
    lakeOpts, leanOpts, reconfigure
    remoteUrl? := dep.remoteUrl?
  }
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
  let (root, env?) ← loadPackageCore "[root]" config
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

/-- Loads a Lake package as a single independent object (without dependencies). -/
def loadPackage (config : LoadConfig) : LogIO Package := do
  Lean.searchPathRef.set config.lakeEnv.leanSearchPath
  (·.1) <$> loadPackageCore "[root]" config

/-- The monad of the dependency resolver. -/
abbrev ResolveT m := CallStackT Name <| StateT Workspace m

/-- Log dependency cycle and error. -/
@[specialize] def depCycleError [MonadError m] (cycle : Cycle Name) : m α :=
  error s!"dependency cycle detected:\n{"\n".intercalate <| cycle.map (s!"  {·}")}"

instance [Monad m] [MonadError m] : MonadCycleOf Name (ResolveT m) where
  throwCycle := depCycleError

/--
Recursively visits the workspace dependency graph, starting from `root`.
At each package, performs `f` to resolve the dependencies of a package,
recurses, then adds the package to workspace's package set.
Errors if a cycle is encountered.

**Traversal Order**

All dependencies of a package are visited in order before recursing to the
dependencies' dependencies. For example, given the dependency graph:

```
R
|- A
|- B
 |- X
 |- Y
|- C
```

Lake follows the order `R`, `A`, `B`, `C`, `X`, `Y`.

The logic behind this design is that users would expect the dependencies
they write in a package configuration to be resolved accordingly and would be
surprised if they are overridden by nested dependencies referring to the same
package.

For example, were Lake to use a pure depth-first traversal, Lake would follow
the order `R`, `A`, `B`, `X`, `Y`, `C`. If `X` and `C` are both the package
`foo`, Lake would use the configuration of `foo` found in `B` rather than in
the root `R`, which would likely confuse the user.
-/
@[inline] def Workspace.resolveDeps
  [Monad m] [MonadError m] (ws : Workspace)
  (f : Package → Dependency → ResolveT m Package)
: m Workspace := do
  let (root, ws) ←
    StateT.run (s := ws) <|
    ReaderT.run (r := []) <|
    StateT.run' (s := {}) <|
    recFetchAcyclic (·.name) go ws.root
  return {ws with root}
where
  @[specialize] go pkg resolve : StateT (NameMap Package) (ResolveT m) Package := do
    pkg.depConfigs.forM fun dep => do
      if (← getThe (NameMap Package)).contains dep.name then
        return
      if (← getThe Workspace).packageMap.contains dep.name then
        return -- already resolved in another branch
      if pkg.name = dep.name then
        error s!"{pkg.name}: package requires itself (or a package with the same name)"
      let dep ← f pkg dep -- package w/o dependencies
      store dep.name dep
    let deps ← pkg.depConfigs.mapM fun dep => do
      if let some dep ← fetch? dep.name then
        modifyThe (NameMap Package) (·.erase dep.name) -- for `dep` linearity
        return OpaquePackage.mk (← resolve dep)
      if let some dep ← findPackage? dep.name then
        return OpaquePackage.mk dep -- already resolved in another branch
      error s!"{dep.name}: impossible resolution state reached"
    let pkg := {pkg with opaqueDeps := deps}
    modifyThe Workspace (·.addPackage pkg)
    return pkg

def stdMismatchError (newName : String) (rev : String) :=
s!"the 'std' package has been renamed to '{newName}' and moved to the
'leanprover-community' organization; downstream packages which wish to
update to the new std should replace

  require std from
    git \"https://github.com/leanprover/std4\"{rev}

in their Lake configuration file with

  require {newName} from
    git \"https://github.com/leanprover-community/{newName}\"{rev}

"

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
  let (ws, entries) ← StateT.run (s := mkNameMap PackageEntry) do
    -- Use manifest versions of root packages that should not be updated
    let rootName := ws.root.name.toString (escape := false)
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
      logInfo s!"{rootName}: no previous manifest, creating one from scratch"
    | .error e =>
      unless toUpdate.isEmpty do
        liftM (m := IO) <| throw e -- only ignore manifest on a bare `lake update`
      logWarning s!"{rootName}: ignoring previous manifest because it failed to load: {e}"
    ws.resolveDeps fun pkg dep => do
      let ws ← getThe Workspace
      let inherited := pkg.name != ws.root.name
      -- Materialize the dependency
      let matDep ← id do
        if let some entry ← fetch? dep.name then
          entry.materialize ws.lakeEnv ws.dir ws.relPkgsDir
        else
          let matDep ← dep.materialize inherited ws.lakeEnv ws.dir ws.relPkgsDir pkg.relDir
          store matDep.name matDep.manifestEntry
          return matDep
      -- Load the package
      let depPkg ← loadDepPackage matDep dep.opts leanOpts reconfigure
      if depPkg.name ≠ dep.name then
        if dep.name = .mkSimple "std" then
          let rev :=
            match matDep.manifestEntry.src with
            | .git (inputRev? := some rev) .. => s!" @ {repr rev}"
            | _ => ""
          logError (stdMismatchError depPkg.name.toString rev)
        if let .error e ← IO.FS.removeDirAll depPkg.dir |>.toBaseIO then -- cleanup
          -- Deleting git repositories via IO.FS.removeDirAll does not work reliably on Windows
          logError s!"'{dep.name}' was downloaded incorrectly; \
            you will need to manually delete '{depPkg.dir}': {e}"
        error s!"{pkg.name}: package '{depPkg.name}' was required as '{dep.name}'"
      -- Add the dependencies' locked dependencies to the manifest
      match (← Manifest.load depPkg.manifestFile |>.toBaseIO) with
      | .ok manifest =>
        manifest.packages.forM fun entry => do
          unless (← getThe (NameMap PackageEntry)).contains entry.name do
            let entry := entry.setInherited.inDirectory depPkg.relDir
            store entry.name entry
      | .error (.noFileOrDirectory ..) =>
        logWarning s!"{depPkg.name}: ignoring missing dependency manifest '{depPkg.manifestFile}'"
      | .error e =>
        logWarning s!"{depPkg.name}: ignoring dependency manifest because it failed to load: {e}"
      return depPkg
  let manifestEntries := ws.packages.foldl (init := #[]) fun arr pkg =>
    match entries.find? pkg.name with
    | some entry => arr.push <|
      entry.setManifestFile pkg.relManifestFile |>.setConfigFile pkg.relConfigFile
    | none => arr -- should only be the case for the root
  let manifest : Manifest := {
    name := ws.root.name
    lakeDir := ws.relLakeDir
    packagesDir? := ws.relPkgsDir
    packages := manifestEntries
  }
  manifest.saveToFile ws.manifestFile
  LakeT.run ⟨ws⟩ <| ws.packages.forM fun pkg => do
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
    match dep.src, entry.src with
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
  ws.resolveDeps fun pkg dep => do
    let ws ← getThe Workspace
    if let some entry := pkgEntries.find? dep.name then
      let result ← entry.materialize ws.lakeEnv ws.dir relPkgsDir
      loadDepPackage result dep.opts leanOpts reconfigure
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
