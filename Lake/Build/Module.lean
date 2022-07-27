/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Elab.Import
import Lake.Build.Index

open System

namespace Lake

/-! # Solo Module Targets -/

def buildModuleUnlessUpToDate (mod : Module)
(dynlibPath : SearchPath) (dynlibs : Array FilePath)
(depTrace : BuildTrace) (leanOnly : Bool) : BuildM BuildTrace := do
  let argTrace : BuildTrace := pureHash mod.leanArgs
  let srcTrace : BuildTrace ← computeTrace mod.leanFile
  let modTrace := (← getLeanTrace).mix <| argTrace.mix <| srcTrace.mix depTrace
  let modUpToDate ← modTrace.checkAgainstFile mod mod.traceFile
  if leanOnly then
    unless modUpToDate do
      compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile none
        (← getLeanPath) mod.rootDir dynlibs dynlibPath mod.leanArgs (← getLean)
  else
    let cUpToDate ← modTrace.checkAgainstFile mod.cFile mod.cTraceFile
    unless modUpToDate && cUpToDate do
      compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile mod.cFile
        (← getLeanPath) mod.rootDir dynlibs dynlibPath mod.leanArgs (← getLean)
    modTrace.writeToFile mod.cTraceFile
  modTrace.writeToFile mod.traceFile
  return mixTrace (← computeTrace mod) depTrace

def Module.mkOleanTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk <| modTarget.bindOpaqueSync fun depTrace =>
    return (self.oleanFile, mixTrace (← computeTrace self.oleanFile) depTrace)

def Module.mkIleanTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk <| modTarget.bindOpaqueSync fun depTrace =>
    return (self.ileanFile, mixTrace (← computeTrace self.ileanFile) depTrace)

def Module.mkCTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk <| modTarget.bindOpaqueSync fun _ =>
    return (self.cFile, mixTrace (← computeTrace self.cFile) (← getLeanTrace))

@[inline] def Module.mkOTarget (cTarget : FileTarget) (self : Module) : FileTarget :=
  leanOFileTarget self.oFile cTarget self.leancArgs

/-! # Recursive Building -/

/-- Compute library directories and build external library targets of the given packages. -/
def recBuildExternalDynlibs (pkgs : Array Package)
: IndexBuildM (Array ActiveDynlibTarget × Array FilePath) := do
  let mut libDirs := #[]
  let mut targets : Array ActiveDynlibTarget := #[]
  for pkg in pkgs do
    libDirs := libDirs.push pkg.libDir
    targets := targets.append <| ← pkg.externLibs.mapM (·.dynlib.recBuild)
  return (targets, libDirs)

/-- Build the dynlibs of the imports that want precompilation (and *their* imports). -/
def recBuildPrecompileDynlibs (pkg : Package) (imports : Array Module)
: IndexBuildM (Array ActiveFileTarget × Array ActiveDynlibTarget × Array FilePath) := do
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty.insert pkg
  let mut modSet := ModuleSet.empty
  let mut targets := #[]
  for imp in imports do
    if imp.shouldPrecompile then
      let (_, transImports) ← imp.imports.recBuild
      for mod in transImports.push imp do
        unless pkgSet.contains mod.pkg do
          pkgSet := pkgSet.insert mod.pkg
          pkgs := pkgs.push mod.pkg
        unless modSet.contains mod do
          modSet := modSet.insert mod
          targets := targets.push <| ← mod.dynlib.recBuild
  return (targets, ← recBuildExternalDynlibs <| pkgs.push pkg)

variable [MonadLiftT BuildM m]

/-- Possible artifacts of the `lean` command. -/
inductive LeanArtifact
| leanBin | olean | ilean | c
deriving Inhabited, Repr, DecidableEq

/--
Recursively build a module and its (transitive, local) imports,
optionally outputting a `.c` file if the modules' is not lean-only or the
requested artifact is `c`. Returns an active target producing the requested
artifact.
-/
def Module.recBuildLean (mod : Module) (art : LeanArtifact)
: IndexBuildM (ActiveBuildTarget (if art = .leanBin then PUnit else FilePath)) := do
  let leanOnly := mod.isLeanOnly ∧ art ≠ .c

  -- Compute and build dependencies
  let extraDepTarget ← mod.pkg.extraDep.recBuild
  let (imports, _) ← mod.imports.recBuild
  let (modTargets, externTargets, libDirs) ← recBuildPrecompileDynlibs mod.pkg imports
  let importTarget ← ActiveTarget.collectOpaqueArray <| ← imports.mapM (·.leanBin.recBuild)
  let externDynlibsTarget ← ActiveTarget.collectArray externTargets
  let modDynlibsTarget ← ActiveTarget.collectArray modTargets

  -- Build Module
  let modTarget : OpaqueTarget := Target.mk do
    importTarget.bindOpaqueAsync fun importTrace => do
    modDynlibsTarget.bindAsync fun modDynlibs modTrace => do
    externDynlibsTarget.bindAsync fun externDynlibs externTrace => do
    extraDepTarget.bindOpaqueSync fun depTrace => do
      let depTrace := importTrace.mix <| modTrace.mix <| externTrace.mix depTrace
      let dynlibPath := libDirs ++ externDynlibs.filterMap ( ·.1)
      -- NOTE: Lean wants the external library symbols before module symbols
      -- NOTE: Unix requires the full file name of the dynlib (Windows doesn't care)
      let dynlibs :=
        externDynlibs.map (.mk <| nameToSharedLib ·.2) ++
        modDynlibs.map (.mk <| nameToSharedLib ·.toString)
      let trace ← buildModuleUnlessUpToDate mod dynlibPath.toList dynlibs depTrace leanOnly
      return ((), trace)
  let modTarget ← modTarget.activate

  -- Save All Resulting Targets & Return Requested One
  store mod.leanBin.key modTarget
  let oleanTarget ← mod.mkOleanTarget (Target.active modTarget) |>.activate
  store mod.olean.key <| oleanTarget
  let ileanTarget ← mod.mkIleanTarget (Target.active modTarget) |>.activate
  store mod.ilean.key <| ileanTarget
  if h : leanOnly then
    have : art ≠ .c := h.2
    return match art with
    | .leanBin => modTarget
    | .olean => oleanTarget
    | .ilean => ileanTarget
  else
    let cTarget ← mod.mkCTarget (Target.active modTarget) |>.activate
    store mod.c.key cTarget
    return match art with
    | .leanBin => modTarget
    | .olean => oleanTarget
    | .ilean => ileanTarget
    | .c => cTarget

/-- The `ModuleFacetConfig` for the builtin `leanBinFacet`. -/
def Module.leanBinFacetConfig : ModuleFacetConfig leanBinFacet :=
  mkFacetTargetConfig (·.recBuildLean .leanBin)

/-- The `ModuleFacetConfig` for the builtin `oleanFacet`. -/
def Module.oleanFacetConfig : ModuleFacetConfig oleanFacet :=
  mkFacetTargetConfig (·.recBuildLean .olean)

/-- The `ModuleFacetConfig` for the builtin `ileanFacet`. -/
def Module.ileanFacetConfig : ModuleFacetConfig ileanFacet :=
  mkFacetTargetConfig (·.recBuildLean .ilean)

/-- The `ModuleFacetConfig` for the builtin `cFacet`. -/
def Module.cFacetConfig : ModuleFacetConfig cFacet :=
  mkFacetTargetConfig (·.recBuildLean .c)

/--
Recursively build the module's object file from its C file produced by `lean`.
-/
def Module.recBuildLeanO (self : Module) : IndexBuildM ActiveFileTarget := do
  self.mkOTarget (Target.active (← self.c.recBuild)) |>.activate

/-- The `ModuleFacetConfig` for the builtin `oFacet`. -/
def Module.oFacetConfig : ModuleFacetConfig oFacet :=
  mkFacetTargetConfig (·.recBuildLeanO)

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
      let (_, impTransImports) ← mod.imports.recBuild
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
: IndexBuildM (Array ActiveFileTarget × Array ActiveDynlibTarget × Array FilePath) := do
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty.insert pkg
  let mut targets := #[]
  for imp in imports do
    unless pkgSet.contains imp.pkg do
      pkgSet := pkgSet.insert imp.pkg
      pkgs := pkgs.push imp.pkg
    targets := targets.push <| ← imp.dynlib.recBuild
  return (targets, ← recBuildExternalDynlibs <| pkgs.push pkg)

/-- Recursively build the shared library of a module (e.g., for `--load-dynlib`). -/
def Module.recBuildDynlib (mod : Module) : IndexBuildM ActiveFileTarget := do

  -- Compute dependencies
  let (_, transImports) ← mod.imports.recBuild
  let linkTargets ← mod.nativeFacets.mapM (recBuild <| mod.facet ·.name)
  let (modTargets, externTargets, pkgLibDirs) ← recBuildDynlibs mod.pkg transImports

  -- Build dynlib
  let linksTarget ← ActiveTarget.collectArray linkTargets
  let modDynlibsTarget ← ActiveTarget.collectArray modTargets
  let externDynlibsTarget : ActiveBuildTarget _  ← ActiveTarget.collectArray externTargets
  let target : BuildTarget _ := Target.mk do
    linksTarget.bindAsync fun links oTrace => do
    modDynlibsTarget.bindAsync fun modDynlibs libTrace => do
    externDynlibsTarget.bindSync fun externDynlibs externTrace => do
      let libNames := modDynlibs ++ externDynlibs.map (.mk ·.2)
      let libDirs := pkgLibDirs ++ externDynlibs.filterMap (·.1)
      let depTrace := oTrace.mix <| libTrace.mix externTrace
      let trace ← buildFileUnlessUpToDate mod.dynlibFile depTrace do
        let args := links.map toString ++
          libDirs.map (s!"-L{·}") ++ libNames.map (s!"-l{·}")
        compileSharedLib mod.dynlibFile args (← getLeanc)
      return (.mk mod.dynlibName, trace)
  target.activate

/-- The `ModuleFacetConfig` for the builtin `dynlibFacet`. -/
def Module.dynlibFacetConfig : ModuleFacetConfig dynlibFacet :=
  mkFacetTargetConfig (·.recBuildDynlib)

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
