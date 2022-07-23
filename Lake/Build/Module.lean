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

def Module.soloTarget (mod : Module) (dynlibs : Array String)
(dynlibPath : SearchPath) (depTarget : BuildTarget x) (leanOnly : Bool) : OpaqueTarget :=
  Target.opaque <| depTarget.bindOpaqueSync fun depTrace => do
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
  Target.mk self.oleanFile <| modTarget.bindOpaqueSync fun depTrace =>
    return mixTrace (← computeTrace self.oleanFile) depTrace

def Module.mkIleanTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk self.ileanFile <| modTarget.bindOpaqueSync fun depTrace =>
    return mixTrace (← computeTrace self.ileanFile) depTrace

def Module.mkCTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk self.cFile <| modTarget.bindOpaqueSync fun _ =>
    return mixTrace (← computeTrace self.cFile) (← getLeanTrace)

@[inline]
def Module.mkOTarget (cTarget : FileTarget) (self : Module) : FileTarget :=
  leanOFileTarget self.oFile cTarget self.leancArgs

@[inline]
def Module.mkDynlibTarget (self : Module) (linkTargets : Array FileTarget)
(libDirs : Array FilePath) (libTargets : Array FileTarget) : FileTarget :=
  let linksTarget : BuildTarget _ := Target.collectArray linkTargets
  let libsTarget : BuildTarget _ := Target.collectArray libTargets
  Target.mk self.dynlibName do
    linksTarget.bindAsync fun links oTrace => do
    libsTarget.bindSync fun libFiles libTrace => do
      buildFileUnlessUpToDate self.dynlibFile (oTrace.mix libTrace) do
        let args := links.map toString ++ libDirs.map (s!"-L{·}") ++ libFiles.map (s!"-l{·}")
        compileSharedLib self.dynlibFile args (← getLeanc)

/-! # Recursive Building -/

/-- Compute library directories and build external library targets of the given packages. -/
def recBuildExternalDynlibs (pkgs : Array Package)
: IndexBuildM (Array ActiveFileTarget × Array FilePath) := do
  let mut libDirs := #[]
  let mut targets : Array ActiveFileTarget := #[]
  for pkg in pkgs do
    libDirs := libDirs.push pkg.libDir
    let externLibTargets ← pkg.externLibs.mapM (·.shared.recBuild)
    for target in externLibTargets do
      if let some parent := target.info.parent then
        libDirs := libDirs.push parent
      if let some stem := target.info.fileStem then
        if Platform.isWindows then
          targets := targets.push <| target.withInfo stem
        else if stem.startsWith "lib" then
          targets := targets.push <| target.withInfo <| stem.drop 3
        else
          logWarning s!"external library `{target.info}` was skipped because it does not start with `lib`"
      else
        logWarning s!"external library `{target.info}` was skipped because it has no file name"
  return (targets, libDirs)

/-- Build the dynlibs of all imports. -/
def recBuildDynlibs (pkg : Package) (imports : Array Module)
: IndexBuildM (Array ActiveFileTarget × Array ActiveFileTarget × Array FilePath) := do
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty.insert pkg
  let mut targets := #[]
  for imp in imports do
    unless pkgSet.contains imp.pkg do
      pkgSet := pkgSet.insert imp.pkg
      pkgs := pkgs.push imp.pkg
    targets := targets.push <| ← imp.dynlib.recBuild
  return (targets, ← recBuildExternalDynlibs <| pkgs.push pkg)

/-- Build the dynlibs of the imports that want precompilation (and *their* imports). -/
def recBuildPrecompileDynlibs (pkg : Package) (imports : Array Module)
: IndexBuildM (Array ActiveFileTarget × Array ActiveFileTarget × Array FilePath) := do
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
  let (modTargets, pkgTargets, libDirs) ← recBuildPrecompileDynlibs mod.pkg imports
  -- NOTE: Lean wants the external library symbols before module symbols
  let dynlibsTarget ← ActiveTarget.collectArray <| pkgTargets ++ modTargets
  let importTarget ← ActiveTarget.collectOpaqueArray
    <| ← imports.mapM (·.leanBin.recBuild)
  let depTarget := Target.active <| ← extraDepTarget.mixOpaqueAsync
    <| ← dynlibsTarget.mixOpaqueAsync importTarget
  -- NOTE: Unix requires the full file name of the dynlib (Windows doesn't care)
  let dynlibs := dynlibsTarget.info.map (nameToSharedLib ·.toString)

  -- Build Module
  let modTarget ← mod.soloTarget dynlibs libDirs.toList depTarget leanOnly |>.activate

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

/--
Recursively build the shared library of a module (e.g., for `--load-dynlib`).
-/
def Module.recBuildDynlib (mod : Module) : IndexBuildM ActiveFileTarget := do
  let (_, transImports) ← mod.imports.recBuild
  let linkTargets ← mod.nativeFacets.mapM fun facet => do
    return Target.active <| ← recBuild <| mod.facet facet.name
  let (modTargets, pkgTargets, libDirs) ← recBuildDynlibs mod.pkg transImports
  let libTargets := modTargets ++ pkgTargets |>.map Target.active
  mod.mkDynlibTarget linkTargets libDirs libTargets |>.activate

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
