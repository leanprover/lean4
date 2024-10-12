/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Gabriel Ebner
-/
import Lake.Config.Monad
import Lake.Util.StoreInsts
import Lake.Build.Topological
import Lake.Load.Materialize
import Lake.Load.Package

open System Lean

/-! # Dependency Resolution

This module contains definitions for resolving the dependencies of a package.
-/

namespace Lake

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
Loads the package configuration of a materialized dependency.
Adds the facets defined in the package to the `Workspace`.
-/
def loadDepPackage
  (dep : MaterializedDep)
  (lakeOpts : NameMap String)
  (leanOpts : Options) (reconfigure : Bool)
: StateT Workspace LogIO Package := fun ws => do
  let name := dep.name.toString (escape := false)
  let (pkg, env?) ← loadPackageCore name {
    lakeEnv := ws.lakeEnv
    wsDir := ws.dir
    relPkgDir := dep.relPkgDir
    relConfigFile := dep.configFile
    lakeOpts, leanOpts, reconfigure
    scope := dep.scope
    remoteUrl := dep.remoteUrl
    targetToolchain? := dep.targetToolchain?
  }
  if let some env := env? then
    let ws ← IO.ofExcept <| ws.addFacetsFromEnv env leanOpts
    return (pkg, ws)
  else
    return (pkg, ws)

/-- The monad of the dependency resolver. -/
abbrev ResolveT m := CallStackT Name <| StateT Workspace m

@[inline] nonrec def ResolveT.run (ws : Workspace) (x : ResolveT m α) (stack : CallStack Name := {}) : m (α × Workspace) :=
  x.run stack |>.run ws

/-- Log dependency cycle and error. -/
@[specialize] def depCycleError [MonadError m] (cycle : Cycle Name) : m α :=
  error s!"dependency cycle detected:\n{"\n".intercalate <| cycle.map (s!"  {·}")}"

instance [Monad m] [MonadError m] : MonadCycleOf Name (ResolveT m) where
  throwCycle := depCycleError

/-- Recursively run a `ResolveT` monad starting from the workspace's root. -/
@[specialize] private def Workspace.runResolveT
  [Monad m] [MonadError m] (ws : Workspace)
  (go : RecFetchFn Package PUnit (ResolveT m))
: m Workspace := do
  let (_, ws) ← ResolveT.run ws <|
    inline <| recFetchAcyclic (·.name) go ws.root
  return ws

/--
Adds monad state that tracks package materialization.
It equips the monad with a map of materialized dependencies.
-/
abbrev MaterializeT := StateT (NameMap MaterializedDep)

@[inline] nonrec def MaterializeT.run' [Functor m] (x : MaterializeT m α) (init : NameMap MaterializedDep := {}) : m α :=
  x.run' init

/--
Adds monad state used to update the manifest.
It equips the monad with a map of locked dependencies.
-/
abbrev UpdateT := StateT (NameMap PackageEntry)

@[inline] nonrec def UpdateT.run (x : UpdateT m α) (init : NameMap PackageEntry := {}) : m (α × NameMap PackageEntry) :=
  x.run init

/--
Reuse manifest versions of root packages that should not be updated.
Also, move the packages directory if its location has changed.
-/
private def reuseManifest (ws : Workspace) (toUpdate : NameSet) : UpdateT LogIO PUnit := do
  let rootName := ws.root.name.toString (escape := false)
  match (← Manifest.load ws.manifestFile |>.toBaseIO) with
  | .ok manifest =>
    -- Reuse manifest versions
    unless toUpdate.isEmpty do
      manifest.packages.forM fun entry => do
        unless entry.inherited || toUpdate.contains entry.name do
          store entry.name entry
    -- Move packages directory
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

/-- Add a package dependency's manifest entries to the update state. -/
private def addDependencyEntries (pkg : Package) : UpdateT LogIO PUnit := do
  match (← Manifest.load pkg.manifestFile |>.toBaseIO) with
  | .ok manifest =>
    manifest.packages.forM fun entry => do
      unless (← getThe (NameMap PackageEntry)).contains entry.name do
        let entry := entry.setInherited.inDirectory pkg.relDir
        store entry.name entry
  | .error (.noFileOrDirectory ..) =>
    logWarning s!"{pkg.name}: ignoring missing manifest '{pkg.manifestFile}'"
  | .error e =>
    logWarning s!"{pkg.name}: ignoring manifest because it failed to load: {e}"

/-- Materialize a single dependency, updating it if desired. -/
private def updateAndMaterializeDep
  (ws : Workspace) (pkg : Package) (dep : Dependency)
: UpdateT LogIO MaterializedDep := do
  if let some entry ← fetch? dep.name then
    entry.materialize ws.lakeEnv ws.dir ws.relPkgsDir
  else
    let inherited := pkg.name ≠ ws.root.name
    let matDep ← dep.materialize inherited ws.lakeEnv ws.dir ws.relPkgsDir pkg.relDir
    store matDep.name matDep.manifestEntry
    return matDep

/-- Verify that a dependency was loaded with the correct name. -/
def validateDep
  (pkg : Package) (dep : Dependency) (matDep : MaterializedDep) (depPkg : Package)
: LogIO PUnit := do
  if depPkg.name ≠ dep.name then
    if dep.name = .mkSimple "std" then
      let rev :=
        match matDep.manifestEntry.src with
        | .git (inputRev? := some rev) .. => s!" @ {repr rev}"
        | _ => ""
      logError (stdMismatchError depPkg.name.toString rev)
    if matDep.manifestEntry.src matches .git .. then
      if let .error e ← IO.FS.removeDirAll depPkg.dir |>.toBaseIO then -- cleanup
        -- Deleting git repositories via IO.FS.removeDirAll does not work reliably on Windows
        logError s!"'{dep.name}' was downloaded incorrectly; \
          you will need to manually delete '{depPkg.dir}': {e}"
    error s!"{pkg.name}: package '{depPkg.name}' was required as '{dep.name}'"

/-- Materialize the missing direct dependencies of `pkg`, updating them if desired. -/
private def updateAndMaterializeDeps
  (ws : Workspace) (pkg : Package)
: MaterializeT (UpdateT LogIO) PUnit := do
  pkg.depConfigs.forM fun dep => do
    if (← get).contains dep.name then
      return
    if ws.packageMap.contains dep.name then
      return -- already handled in another branch
    if pkg.name = dep.name then
      error s!"{pkg.name}: package requires itself (or a package with the same name)"
    let matDep ← updateAndMaterializeDep ws pkg dep
    store dep.name matDep

/-- The full dependency resolver monad. -/
abbrev ResolveM := ResolveT (MaterializeT (UpdateT LogIO))

/-- Recursively load the dependency of `pkg` into the workspace. -/
private def recLoadDeps
  (pkg : Package) (recurse : Package → ResolveM PUnit) (leanOpts : Options := {})
: ResolveM PUnit := do
  pkg.depConfigs.forM fun dep => do
    if let some matDep ← fetch? dep.name then
      modifyThe (NameMap MaterializedDep) (·.erase dep.name) -- for `dep` linearity
      let depPkg ← loadDepPackage matDep dep.opts leanOpts true
      validateDep pkg dep matDep depPkg
      addDependencyEntries depPkg
      recurse depPkg
    else if (← getThe Workspace).packageMap.contains dep.name then
      return -- already loaded in another branch
    else
      error s!"{dep.name}: impossible resolution state reached"
  modifyThe Workspace (·.addPackage pkg)

/--
Recursively visits the workspace dependency graph, starting from `root`.
At each package, loops through each direct dependency performing just `breath`.
Them, loops again through the results applying `depth`, recursing, and adding
the package to workspace's package set. Errors if a cycle is encountered.

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
@[inline] private def Workspace.updateDeps
  (ws : Workspace) (leanOpts : Options := {})
: UpdateT LogIO Workspace := do
  MaterializeT.run' <| ws.runResolveT fun pkg visit => do
    updateAndMaterializeDeps (← getWorkspace) pkg
    recLoadDeps pkg visit leanOpts


/-- Write package entries to the workspace manifest. -/
def Workspace.writeManifest
  (ws : Workspace) (entries : NameMap PackageEntry)
: LogIO PUnit := do
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

/--
Rebuild the workspace's Lake manifest and materialize missing dependencies.

Packages are updated to latest specific revision matching that in `require`
(e.g., if the `require` is `@master`, update to latest commit on master) or
removed if the `require` is removed. If `tuUpdate` is empty, update/remove all
root dependencies. Otherwise, only update the root dependencies specified.

Dependencies are always reconfigured on update.
-/
def Workspace.updateAndMaterialize
  (ws : Workspace) (toUpdate : NameSet := {}) (leanOpts : Options := {})
: LogIO Workspace := do
  let (ws, entries) ← UpdateT.run do
    reuseManifest ws toUpdate
    ws.updateDeps leanOpts
  ws.writeManifest entries
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
    let some src := dep.src? | return
    let some entry := pkgEntries.find? dep.name | return
    match src, entry.src with
    | .git (url := url) (rev := rev) .., .git (url := url') (inputRev? := rev')  .. =>
      if url ≠ url' then warnOutOfDate "git url"
      if rev ≠ rev' then warnOutOfDate "git revision"
    | .path .., .path .. => pure ()
    | _, _ => warnOutOfDate "source kind (git/path)"

/--
Recursively visits the workspace dependency graph, starting from `root`,
loading dependencies as packages via the `load` function.

This is a simpler version of the `updateDeps` function used
when the dependencies have already been resolved.
-/
@[inline] private def Workspace.loadDeps
  [Monad m] [MonadError m] (ws : Workspace)
  (load : Package → Dependency → StateT Workspace m Package)
: m Workspace := do
  ws.runResolveT go
where
  @[specialize] go pkg recurse : ResolveT m Unit := do
    pkg.depConfigs.forM fun dep => do
      unless (← getWorkspace).packageMap.contains dep.name do
        let depPkg ← load pkg dep
        recurse depPkg
    modifyThe Workspace (·.addPackage pkg)

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
  ws.loadDeps fun pkg dep => do
    let ws ← getWorkspace
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
