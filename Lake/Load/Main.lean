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
def loadDepsFromEnv (env : Environment) (opts : Options) : Except String (Array Dependency) := do
  packageDepAttr.ext.getState env |>.foldM (init := #[]) fun arr name => do
    return arr.push <| ← evalConstCheck env opts Dependency ``Dependency name

/--
Resolve a single dependency and load the resulting package.
Resolution is based on the `Dependency` configuration and the package manifest.
-/
def resolveDep (packagesDir : FilePath) (pkg : Package) (dep : Dependency)
(topLevel : Bool) (shouldUpdate : Bool) : StateT Manifest LogIO Package := do
  let entry? := (← get).find? dep.name
  let entry? := entry?.map fun entry =>
    {entry with shouldUpdate := if topLevel then shouldUpdate else entry.shouldUpdate}
  let ⟨dir, url?, tag?, entry?⟩ ← materializeDep packagesDir pkg.dir dep entry?
  let configEnv ← elabConfigFile dir dep.options pkg.leanOpts (dir / defaultConfigFile)
  let config ← IO.ofExcept <| PackageConfig.loadFromEnv configEnv pkg.leanOpts
  let depPkg : Package := {
    dir, config, configEnv,
    leanOpts := pkg.leanOpts
    remoteUrl? := url?, gitTag? := tag?
  }
  unless depPkg.name = dep.name do
    error <|
      s!"{pkg.name} (in {pkg.dir}) depends on {dep.name}, " ++
      s!"but resolved dependency has name {depPkg.name} (in {dir})"
  if let some entry := entry? then
    modify (·.insert entry)
  let depManifest ← Manifest.loadOrEmpty depPkg.manifestFile
  for depEntry in depManifest do
    if let some entry := (← get).find? depEntry.name then
      let shouldUpdate :=
        match entry.inputRev?, depEntry.inputRev? with
        | none,     none     => entry.rev != depEntry.rev
        | none,     some _   => false
        | some _,   none     => false
        | some rev, some dep => rev = dep ∧ entry.rev ≠ depEntry.rev
      let contributors := entry.contributors.insert depPkg.name depEntry.toPersistentPackageEntry
      modify (·.insert {entry with contributors, shouldUpdate})
    else
      let contributors := NameMap.empty.insert depPkg.name depEntry.toPersistentPackageEntry
      modify (·.insert {depEntry with contributors})
  return depPkg

/--
Resolves the package's dependencies,
downloading and/or updating them as necessary.
-/
def Package.resolveDeps (root : Package) (shouldUpdate := true) : LogIO Package := do
  let manifest ← Manifest.loadOrEmpty root.manifestFile
  let (root, manifest) ← StateT.run (s := manifest) do
    let res ← EStateT.run' (mkNameMap Package) do
      buildAcyclic (·.name) root fun pkg resolve => do
        let topLevel := pkg.name = root.name
        let deps ← IO.ofExcept <| loadDepsFromEnv pkg.configEnv pkg.leanOpts
        let depPkgs ← deps.mapM fun dep => do
          fetchOrCreate dep.name do
            liftM <| resolveDep root.packagesDir pkg dep topLevel shouldUpdate
        return {pkg with opaqueDeps := ← depPkgs.mapM (.mk <$> resolve ·)}
    match res with
    | Except.ok root =>
      return root
    | Except.error cycle =>
      let cycle := cycle.map (s!"  {·}")
      error s!"dependency cycle detected:\n{"\n".intercalate cycle}"
  unless manifest.isEmpty do
    if (← getIsVerbose) ∨ shouldUpdate then
      for entry in manifest do
        let mut log := s!"Found dependency `{entry.name}`\n"
        for (name, contrib) in entry.contributors do
          let inputRev := contrib.inputRev?.getD Git.upstreamBranch
          log := log ++ s!"`{name}` locked `{inputRev}` at `{contrib.rev}`\n"
        let inputRev := entry.inputRev?.getD Git.upstreamBranch
        log := log ++  s!"Using `{inputRev}` at `{entry.rev}`"
        logInfo log
    manifest.saveToFile root.manifestFile
  return root

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
Load a `Workspace` for a Lake package by
elaborating its configuration file and resolving its dependencies.
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
  let root ← root.resolveDeps config.updateDeps
  {ws with root}.finalize
