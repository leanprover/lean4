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
  let (_, ws) ← ResolveT.run ws do
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
private def validateDep
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

/--
Exit code returned if Lake needs a manual restart.
Used, for instance, if the toolchain is updated and no Elan is detected.
-/
def restartCode : ExitCode := 4

/--
Update the workspace's `lean-toolchain` if necessary.

Compares the root's toolchain with that of its direct dependencies to find the
best match. If none can be found, issue warning and return normally. If an
update is found
-/
def Workspace.updateToolchain
  (ws : Workspace) (rootDeps : Array MaterializedDep)
: LogIO PUnit := do
  logInfo "checking for toolchain updates..."
  let rootToolchainFile := ws.root.dir / toolchainFileName
  let rootTc? := ws.root.targetToolchain?
  let (src, tc?, tcs) := rootDeps.foldl (init := (ws.root.name, rootTc?, #[])) fun (src, tc?, tcs) dep =>
    let depTc? := dep.targetToolchain?
    if let some depTc := depTc? then
      if let some tc := tc? then
        if depTc ≤ tc then
          (src, some tc, tcs)
        else if tc < depTc then
          (dep.name, some depTc, tcs)
        else
          (src, tc, tcs.push (dep.name, depTc))
      else
        (dep.name, depTc?, tcs)
    else
      (src, tc?, tcs)
  if 0 < tcs.size then
    let s := "toolchain not updated; multiple toolchain candidates:"
    let s := if let some tc := tc? then s!"{s}\n  {tc}\n    from {src}" else s
    let s := tcs.foldl (init := s) fun s (d, tc) => s!"{s}\n  {tc}\n    from {d}"
    logWarning s
  else if tc? == rootTc? then
    logInfo "toolchain not updated; already up-to-date"
  else if let some tc := tc? then
    IO.FS.writeFile rootToolchainFile tc.toString
    if let some elanInstall := ws.lakeEnv.elan? then
      if let some lakeArgs := ws.lakeArgs? then
        logInfo s!"toolchain updated to '{tc}'; restarting Lake"
        let elanArgs := #["run", "--install", tc.toString, "lake"]
        let args := elanArgs ++ #["--keep-toolchain"] ++ lakeArgs
        let child ← IO.Process.spawn {cmd := elanInstall.elan.toString, args}
        IO.Process.exit (← child.wait).toUInt8
      else
        logInfo s!"toolchain updated to '{tc}'; \
          you will need to manually restart Lake"
        IO.Process.exit restartCode.toUInt8
    else
      logInfo s!"toolchain updated to '{tc}'; \
        you will need to manually restart Lake (no Elan detected)"
      IO.Process.exit restartCode.toUInt8
  else if !ws.lakeEnv.toolchain.isEmpty then
    IO.FS.writeFile rootToolchainFile ws.lakeEnv.toolchain
    logInfo s!"toolchain not updated; wrote current toolchain to {rootToolchainFile}"
  else
    logInfo s!"toolchain not updated; no toolchain information found"

/--
Updates the workspace, materializing and reconfiguring dependencies.

Dependencies are updated to latest specific revision matching that in `require`
(e.g., if the `require` is `@master`, update to latest commit on master) or
removed if the `require` is removed.
If `tuUpdate` is empty, all direct dependencies of the workspace's root will be
updated and/or remove. Otherwise, only those specified will be updated.

If `updateToolchain := true`, the workspace's toolchain is also updated to the
latest toolchain compatible with the root and its direct dependencies.
If there are multiple incomparable toolchain versions across them,
a warning will be issued and no update performed.
If an update is performed, Lake will automatically restart the update on the new
toolchain (via `elan`). If `elan` is missing, it will instead request a manual
restart from the user and exit immediately with `restartCode`.

**Dependency Traversal Order**

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
def Workspace.updateAndMaterializeCore
  (ws : Workspace)
  (toUpdate : NameSet := {}) (leanOpts : Options := {})
  (updateToolchain := true)
: LogIO  (Workspace × NameMap PackageEntry) := UpdateT.run do
  reuseManifest ws toUpdate
  let depMap ← id do
    if updateToolchain then
      let rootDeps ← ws.root.depConfigs.mapM fun dep =>
        updateAndMaterializeDep ws ws.root dep
      ws.updateToolchain rootDeps
      return rootDeps.foldl (init := {}) fun m d => m.insert d.name d
    else
      return {}
  MaterializeT.run' (init := depMap) do ws.runResolveT go
where
  @[specialize] go pkg recurse := do
    -- Materialize the missing direct dependencies of `pkg`, updating them if desired.
    pkg.depConfigs.forM fun dep => do
      if (← getThe (NameMap MaterializedDep)).contains dep.name then
        return
      if ws.packageMap.contains dep.name then
        return -- already handled in another branch
      if pkg.name = dep.name then
        error s!"{pkg.name}: package requires itself (or a package with the same name)"
      let matDep ← updateAndMaterializeDep ws pkg dep
      store dep.name matDep
    -- Recursively load the dependency of `pkg` into the workspace.
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
Updates the workspace, writes the new Lake manifest, and runs package
post-update hooks.

See `Workspace.updateAndMaterializeCore` for details on the update process.
-/
def Workspace.updateAndMaterialize
  (ws : Workspace)
  (toUpdate : NameSet := {}) (leanOpts : Options := {})
  (updateToolchain := true)
: LogIO Workspace := do
  let (ws, entries) ←
    ws.updateAndMaterializeCore toUpdate leanOpts updateToolchain
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
