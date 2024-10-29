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
  }
  if let some env := env? then
    let ws ← IO.ofExcept <| ws.addFacetsFromEnv env leanOpts
    return (pkg, ws)
  else
    return (pkg, ws)

/--
The resolver's call stack of dependencies.
That is, the dependency currently being resolved plus its parents.
-/
abbrev DepStack := CallStack Name

/--
A monad transformer for recursive dependency resolution.
It equips the monad with the stack of dependencies currently being resolved.
-/
abbrev DepStackT m := CallStackT Name m

@[inline] nonrec def DepStackT.run
  (x : DepStackT m α) (stack : DepStack := {})
: m α :=
  x.run stack

/-- Log dependency cycle and error. -/
@[specialize] def depCycleError [MonadError m] (cycle : Cycle Name) : m α :=
  error s!"dependency cycle detected:\n{"\n".intercalate <| cycle.map (s!"  {·}")}"

instance [Monad m] [MonadError m] : MonadCycleOf Name (DepStackT m) where
  throwCycle := depCycleError

/-- The monad of the dependency resolver. -/
abbrev ResolveT m := DepStackT <| StateT Workspace m

@[inline] nonrec def ResolveT.run
  (ws : Workspace) (x : ResolveT m α) (stack : DepStack := {})
: m (α × Workspace) :=
  x.run stack |>.run ws

/-- Recursively run a `ResolveT` monad starting from the workspace's root. -/
@[specialize] private def Workspace.runResolveT
  [Monad m] [MonadError m] (ws : Workspace)
  (go : RecFetchFn Package PUnit (ResolveT m))
  (root := ws.root) (stack : DepStack  := {})
: m Workspace := do
  let (_, ws) ← ResolveT.run ws (stack := stack) do
    inline <| recFetchAcyclic (·.name) go root
  return ws

/-
Recursively visits each node in a package's dependency graph, starting from
the workspace package `root`. Each dependency missing from the workspace is
resolved using the `resolve` function and added into the workspace.

Recursion occurs breadth-first. Each direct dependency of a package is
resolved in reverse order before recursing to the dependencies' dependencies.

See `Workspace.updateAndMaterializeCore` for more details.
-/
@[inline] private def Workspace.resolveDepsCore
  [Monad m] [MonadError m] (ws : Workspace)
  (load : Package → Dependency → StateT Workspace m Package)
  (root : Package := ws.root) (stack : DepStack := {})
: m Workspace := do
  ws.runResolveT go root stack
where
  @[specialize] go pkg recurse : ResolveT m Unit := do
    let start := (← getWorkspace).packages.size
    -- Materialize and load the missing direct dependencies of `pkg`
    pkg.depConfigs.forRevM fun dep => do
      let ws ← getWorkspace
      if ws.packageMap.contains dep.name then
        return -- already handled in another branch
      if pkg.name = dep.name then
        error s!"{pkg.name}: package requires itself (or a package with the same name)"
      let depPkg ← load pkg dep
      modifyThe Workspace (·.addPackage depPkg)
    -- Recursively load the dependencies' dependencies
    (← getWorkspace).packages.forM recurse start

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
private def reuseManifest
  (ws : Workspace) (toUpdate : NameSet)
: UpdateT LogIO PUnit := do
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
    /-
    NOTE: A path dependency inherited from another dependency's manifest
    will always be of the form a `./<relPath>` (i.e., be relative to its
    workspace).  Thus, when relativized to this workspace, it will have the
    path  `<relPkgDir>/./<relPath>`. However, if defining dependency lacks
    a manifest, it will instead be locked as `<relPkgDir>/<relPath>`.
    Adding a `.` here eliminates this difference.
    -/
    let relPkgDir := if pkg.relDir == "." then pkg.relDir else pkg.relDir / "."
    let matDep ← dep.materialize inherited ws.lakeEnv ws.dir ws.relPkgsDir relPkgDir
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
: LoggerIO PUnit := do
  let rootToolchainFile := ws.root.dir / toolchainFileName
  let rootTc? ← ToolchainVer.ofDir? ws.dir
  let (src, tc?, tcs) ← rootDeps.foldlM (init := (ws.root.name, rootTc?, #[])) fun s dep => do
    let depTc? ← ToolchainVer.ofDir? (ws.dir / dep.relPkgDir)
    let some depTc := depTc?
      | return s
    let (src, tc?, tcs) := s
    let some tc := tc?
      | return (dep.name, depTc?, tcs)
    if depTc ≤ tc then
      return (src, tc, tcs)
    else if tc < depTc then
      return (dep.name, depTc, tcs)
    else
      return (src, tc, tcs.push (dep.name, depTc))
  if 0 < tcs.size then
    let s := "toolchain not updated; multiple toolchain candidates:"
    let s := if let some tc := tc? then s!"{s}\n  {tc}\n    from {src}" else s
    let s := tcs.foldl (init := s) fun s (d, tc) => s!"{s}\n  {tc}\n    from {d}"
    logWarning s
  else if let some tc := tc? then
    if rootTc?.any (· == tc) then
      logInfo "toolchain not updated; already up-to-date"
      return
    logInfo s!"updating toolchain to '{tc}'"
    IO.FS.writeFile rootToolchainFile tc.toString
    let some lakeArgs := ws.lakeArgs?
      | logInfo s!"cannot auto-restart; you will need to manually restart Lake"
        IO.Process.exit restartCode.toUInt8
    let some elanInstall := ws.lakeEnv.elan?
      | logInfo s!"no Elan detected; you will need to manually restart Lake"
        IO.Process.exit restartCode.toUInt8
    logInfo s!"restarting Lake via Elan"
    let child ← IO.Process.spawn {
      cmd := elanInstall.elan.toString
      args := #["run", "--install", tc.toString, "lake"] ++ lakeArgs
      env := Env.noToolchainVars
    }
    IO.Process.exit (← child.wait).toUInt8
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

All dependencies of a package are visited in reverse order before recursing
to the dependencies' dependencies. For example, given the dependency graph:

```
R
|- A
|- B
 |- X
 |- Y
|- C
```

Lake follows the order `R`, `C`, `A`, `B`, `Y`, `X`.

The reason for this is two-fold:
1. Like targets, later requires should shadow earlier definitions.
2. Requires written by a user should take priority over those inherited
from dependencies.

Were Lake to use a depth-first traversal, for example, Lake would follow
the order `R`, `A`, `B`, `X`, `Y`, `C`. If `X` and `C` are both the package
`foo`, Lake would use the configuration of `foo` found in `B` rather than in
the root `R`, which would likely confuse the user.
-/
def Workspace.updateAndMaterializeCore
  (ws : Workspace)
  (toUpdate : NameSet := {}) (leanOpts : Options := {})
  (updateToolchain := true)
: LoggerIO (Workspace × NameMap PackageEntry) := UpdateT.run do
  reuseManifest ws toUpdate
  let ws := ws.addPackage ws.root
  if updateToolchain then
    let deps := ws.root.depConfigs.reverse
    let matDeps ← deps.mapM fun dep => do
      logVerbose s!"{ws.root.name}: updating '{dep.name}' with {toJson dep.opts}"
      updateAndMaterializeDep ws ws.root dep
    ws.updateToolchain matDeps
    let start := ws.packages.size
    let ws ← (deps.zip matDeps).foldlM (init := ws) fun ws (dep, matDep) => do
      let (depPkg, ws) ← loadUpdatedDep ws.root dep matDep ws
      let ws := ws.addPackage depPkg
      return ws
    ws.packages.foldlM (init := ws) (start := start) fun ws pkg =>
      ws.resolveDepsCore (stack := [ws.root.name]) updateAndLoadDep pkg
  else
    ws.resolveDepsCore updateAndLoadDep
where
  @[inline] updateAndLoadDep pkg dep := do
    let matDep ← updateAndMaterializeDep (← getWorkspace) pkg dep
    loadUpdatedDep pkg dep matDep
  @[inline] loadUpdatedDep pkg dep matDep : StateT Workspace (UpdateT LogIO) Package  := do
    let depPkg ← loadDepPackage matDep dep.opts leanOpts true
    validateDep pkg dep matDep depPkg
    addDependencyEntries depPkg
    return depPkg

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

/-- Run a package's `post_update` hooks. -/
def Package.runPostUpdateHooks (pkg : Package) : LakeT LogIO PUnit := do
  unless pkg.postUpdateHooks.isEmpty do
  logInfo s!"{pkg.name}: running post-update hooks"
  pkg.postUpdateHooks.forM fun hook => hook.get.fn pkg

/--
Updates the workspace, writes the new Lake manifest, and runs package
post-update hooks.

See `Workspace.updateAndMaterializeCore` for details on the update process.
-/
def Workspace.updateAndMaterialize
  (ws : Workspace)
  (toUpdate : NameSet := {}) (leanOpts : Options := {})
  (updateToolchain := true)
: LoggerIO Workspace := do
  let (ws, entries) ←
    ws.updateAndMaterializeCore toUpdate leanOpts updateToolchain
  ws.writeManifest entries
  ws.runLakeT do ws.packages.forM (·.runPostUpdateHooks)
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
  let ws := ws.addPackage ws.root
  ws.resolveDepsCore fun pkg dep => do
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
