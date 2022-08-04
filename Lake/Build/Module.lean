/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Elab.Import
import Lake.Build.Common

open System

namespace Lake

def Module.buildUnlessUpToDate (mod : Module)
(dynlibPath : SearchPath) (dynlibs : Array FilePath)
(depTrace : BuildTrace) (leanOnly : Bool) : BuildM BuildTrace := do
  let isOldMode ← getIsOldMode
  let argTrace : BuildTrace := pureHash mod.leanArgs
  let srcTrace : BuildTrace ← computeTrace mod.leanFile
  let modTrace := (← getLeanTrace).mix <| argTrace.mix <| srcTrace.mix depTrace
  let modUpToDate ← do
    if isOldMode then
      srcTrace.checkAgainstTime mod
    else
      modTrace.checkAgainstFile mod mod.traceFile
  let name := mod.name.toString
  if leanOnly then
    unless modUpToDate do
      compileLeanModule name mod.leanFile mod.oleanFile mod.ileanFile none
        (← getLeanPath) mod.rootDir dynlibs dynlibPath mod.leanArgs (← getLean)
  else
    let cUpToDate ←
      if isOldMode then
        pure modUpToDate
      else
        (modUpToDate && ·) <$> modTrace.checkAgainstFile mod.cFile mod.cTraceFile
    unless cUpToDate do
      compileLeanModule name mod.leanFile mod.oleanFile mod.ileanFile mod.cFile
        (← getLeanPath) mod.rootDir dynlibs dynlibPath mod.leanArgs (← getLean)
    unless isOldMode do
      modTrace.writeToFile mod.cTraceFile
  unless isOldMode do
    modTrace.writeToFile mod.traceFile
  return mixTrace (← computeTrace mod) depTrace

/-- Compute library directories and build external library Jobs of the given packages. -/
def recBuildExternalDynlibs (pkgs : Array Package)
: IndexBuildM (Array (BuildJob Dynlib) × Array FilePath) := do
  let mut libDirs := #[]
  let mut jobs : Array (BuildJob Dynlib) := #[]
  for pkg in pkgs do
    libDirs := libDirs.push pkg.libDir
    jobs := jobs.append <| ← pkg.externLibs.mapM (·.dynlib.fetch)
  return (jobs, libDirs)

/-- Build the dynlibs of the imports that want precompilation (and *their* imports). -/
def recBuildPrecompileDynlibs (pkg : Package) (imports : Array Module)
: IndexBuildM (Array (BuildJob String) × Array (BuildJob Dynlib) × Array FilePath) := do
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty.insert pkg
  let mut modSet := ModuleSet.empty
  let mut jobs := #[]
  for imp in imports do
    if imp.shouldPrecompile then
      let (_, transImports) ← imp.imports.fetch
      for mod in transImports.push imp do
        unless pkgSet.contains mod.pkg do
          pkgSet := pkgSet.insert mod.pkg
          pkgs := pkgs.push mod.pkg
        unless modSet.contains mod do
          modSet := modSet.insert mod
          jobs := jobs.push <| ← mod.dynlib.fetch
  return (jobs, ← recBuildExternalDynlibs <| pkgs.push pkg)

variable [MonadLiftT BuildM m]

/-- Possible artifacts of the `lean` command. -/
inductive LeanArtifact
| leanBin | olean | ilean | c
deriving Inhabited, Repr, DecidableEq

/--
Recursively build a module and its (transitive, local) imports,
optionally outputting a `.c` file if the modules' is not lean-only or the
requested artifact is `c`. Returns an build job producing the requested
artifact.
-/
def Module.recBuildLean (mod : Module) (art : LeanArtifact)
: IndexBuildM (BuildJob (if art = .leanBin then Unit else FilePath)) := do
  let leanOnly := mod.isLeanOnly ∧ art ≠ .c

  -- Compute and build dependencies
  let (imports, _) ← mod.imports.fetch
  let extraDepJob ← mod.pkg.extraDep.fetch
  let (modJobs, externJobs, libDirs) ← recBuildPrecompileDynlibs mod.pkg imports
  let importJob ← BuildJob.mixArray <| ← imports.mapM (·.leanBin.fetch)
  let externDynlibsJob ← BuildJob.collectArray externJobs
  let modDynlibsJob ← BuildJob.collectArray modJobs

  -- Build Module
  let modJob : BuildJob Unit ← show SchedulerM _ from do
    extraDepJob.bindAsync fun _ _ => do
    importJob.bindAsync fun _ importTrace => do
    modDynlibsJob.bindAsync fun modDynlibs modTrace => do
    externDynlibsJob.bindSync fun externDynlibs externTrace => do
      let depTrace := importTrace.mix <| modTrace.mix externTrace
      let dynlibPath := libDirs ++ externDynlibs.filterMap ( ·.1) |>.toList
      -- NOTE: Lean wants the external library symbols before module symbols
      -- NOTE: Unix requires the full file name of the dynlib (Windows doesn't care)
      let dynlibs :=
        externDynlibs.map (.mk <| nameToSharedLib ·.2) ++
        modDynlibs.map (.mk <| nameToSharedLib ·)
      let trace ← mod.buildUnlessUpToDate dynlibPath dynlibs depTrace leanOnly
      return ((), trace)

  -- Save All Resulting Jobs & Return Requested One
  store mod.leanBin.key modJob
  let oleanJob ← modJob.bindSync fun _ depTrace =>
    return (mod.oleanFile, mixTrace (← computeTrace mod.oleanFile) depTrace)
  store mod.olean.key <| oleanJob
  let ileanJob ← modJob.bindSync fun _ depTrace =>
    return (mod.ileanFile, mixTrace (← computeTrace mod.ileanFile) depTrace)
  store mod.ilean.key <| ileanJob
  if h : leanOnly then
    have : art ≠ .c := h.2
    return match art with
    | .leanBin => modJob
    | .olean => oleanJob
    | .ilean => ileanJob
  else
    let cJob ← modJob.bindSync fun _  _ =>
      return (mod.cFile, mixTrace (← computeTrace mod.cFile) (← getLeanTrace))
    store mod.c.key cJob
    return match art with
    | .leanBin => modJob
    | .olean => oleanJob
    | .ilean => ileanJob
    | .c => cJob

/-- The `ModuleFacetConfig` for the builtin `leanBinFacet`. -/
def Module.leanBinFacetConfig : ModuleFacetConfig leanBinFacet :=
  mkFacetJobConfig (·.recBuildLean .leanBin)

/-- The `ModuleFacetConfig` for the builtin `oleanFacet`. -/
def Module.oleanFacetConfig : ModuleFacetConfig oleanFacet :=
  mkFacetJobConfig (·.recBuildLean .olean)

/-- The `ModuleFacetConfig` for the builtin `ileanFacet`. -/
def Module.ileanFacetConfig : ModuleFacetConfig ileanFacet :=
  mkFacetJobConfig (·.recBuildLean .ilean)

/-- The `ModuleFacetConfig` for the builtin `cFacet`. -/
def Module.cFacetConfig : ModuleFacetConfig cFacet :=
  mkFacetJobConfig (·.recBuildLean .c)

/-- Recursively build the module's object file from its C file produced by `lean`. -/
def Module.recBuildLeanO (self : Module) : IndexBuildM (BuildJob FilePath) := do
  buildLeanO self.name.toString self.oFile (← self.c.fetch) self.leancArgs

/-- The `ModuleFacetConfig` for the builtin `oFacet`. -/
def Module.oFacetConfig : ModuleFacetConfig oFacet :=
  mkFacetJobConfig Module.recBuildLeanO

/--
Recursively parse the Lean files of a module and its imports
building an `Array` product of its direct and transitive local imports.
-/
def Module.recParseImports (mod : Module)
: IndexBuildM (Array Module × Array Module) := do
  let mut transImports := #[]
  let mut directImports := #[]
  let mut importSet := ModuleSet.empty
  let contents ← IO.FS.readFile mod.leanFile
  let (imports, _, _) ← Lean.Elab.parseImports contents mod.leanFile.toString
  for imp in imports do
    if let some mod ← findModule? imp.module then
      let (_, impTransImports) ← mod.imports.fetch
      for transImp in impTransImports do
        unless importSet.contains transImp do
          importSet := importSet.insert transImp
          transImports := transImports.push transImp
      unless importSet.contains mod do
        importSet := importSet.insert mod
        transImports := transImports.push mod
      directImports := directImports.push mod
  return (directImports, transImports)

/-- The `ModuleFacetConfig` for the builtin `importFacet`. -/
def Module.importFacetConfig : ModuleFacetConfig importFacet :=
  mkFacetConfig (·.recParseImports)

/-- Build the dynlibs of all imports. -/
def recBuildDynlibs (pkg : Package) (imports : Array Module)
: IndexBuildM (Array (BuildJob String) × Array (BuildJob Dynlib) × Array FilePath) := do
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty.insert pkg
  let mut jobs := #[]
  for imp in imports do
    unless pkgSet.contains imp.pkg do
      pkgSet := pkgSet.insert imp.pkg
      pkgs := pkgs.push imp.pkg
    jobs := jobs.push <| ← imp.dynlib.fetch
  return (jobs, ← recBuildExternalDynlibs <| pkgs.push pkg)

/-- Recursively build the shared library of a module (e.g., for `--load-dynlib`). -/
def Module.recBuildDynlib (mod : Module) : IndexBuildM (BuildJob String) := do

  -- Compute dependencies
  let (_, transImports) ← mod.imports.fetch
  let linkJobs ← mod.nativeFacets.mapM (fetch <| mod.facet ·.name)
  let (modJobs, externJobs, pkgLibDirs) ← recBuildDynlibs mod.pkg transImports

  -- Collect Jobs
  let linksJob ← BuildJob.collectArray linkJobs
  let modDynlibsJob ← BuildJob.collectArray modJobs
  let externDynlibsJob ← BuildJob.collectArray externJobs

  -- Build dynlib
  show SchedulerM _ from do
  linksJob.bindAsync fun links oTrace => do
  modDynlibsJob.bindAsync fun modDynlibs libTrace => do
  externDynlibsJob.bindSync fun externDynlibs externTrace => do
    let libNames := modDynlibs ++ externDynlibs.map (·.2)
    let libDirs := pkgLibDirs ++ externDynlibs.filterMap (·.1)
    let depTrace := oTrace.mix <| libTrace.mix externTrace
    let trace ← buildFileUnlessUpToDate mod.dynlibFile depTrace do
      let args := links.map toString ++
        libDirs.map (s!"-L{·}") ++ libNames.map (s!"-l{·}")
      compileSharedLib mod.name.toString mod.dynlibFile args (← getLeanc)
    return (mod.dynlibName, trace)

/-- The `ModuleFacetConfig` for the builtin `dynlibFacet`. -/
def Module.dynlibFacetConfig : ModuleFacetConfig dynlibFacet :=
  mkFacetJobConfig Module.recBuildDynlib

open Module in
/--
A name-configuration map for the initial set of
Lake module facets (e.g., `lean.{imports, c, o, dynlib]`).
-/
def initModuleFacetConfigs : DNameMap ModuleFacetConfig :=
  DNameMap.empty
  |>.insert importFacet importFacetConfig
  |>.insert leanBinFacet leanBinFacetConfig
  |>.insert oleanFacet oleanFacetConfig
  |>.insert ileanFacet ileanFacetConfig
  |>.insert cFacet cFacetConfig
  |>.insert oFacet oFacetConfig
  |>.insert dynlibFacet dynlibFacetConfig
