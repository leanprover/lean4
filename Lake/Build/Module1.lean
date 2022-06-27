/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Elab.Import
import Lake.Build.Info
import Lake.Build.Store
import Lake.Build.Targets

open System

namespace Lake

-- # Solo Module Targets

def Module.soloTarget (mod : Module) (dynlibs : Array FilePath)
(dynlibPath : SearchPath) (depTarget : BuildTarget x) (c := true) : OpaqueTarget :=
  Target.opaque <| depTarget.bindOpaqueSync fun depTrace => do
    let argTrace : BuildTrace := pureHash mod.leanArgs
    let srcTrace : BuildTrace ← computeTrace mod.leanFile
    let modTrace := (← getLeanTrace).mix <| argTrace.mix <| srcTrace.mix depTrace
    let modUpToDate ← modTrace.checkAgainstFile mod mod.traceFile
    if c then
      let cUpToDate ← modTrace.checkAgainstFile mod.cFile mod.cTraceFile
      unless modUpToDate && cUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile mod.cFile
          (← getOleanPath) mod.pkg.rootDir dynlibs dynlibPath mod.leanArgs (← getLean)
      modTrace.writeToFile mod.cTraceFile
    else
      unless modUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile none
          (← getOleanPath) mod.pkg.rootDir dynlibs dynlibPath mod.leanArgs (← getLean)
    modTrace.writeToFile mod.traceFile
    return depTrace

def Module.mkCTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk self.cFile <| modTarget.bindOpaqueSync fun _ =>
    return mixTrace (← computeTrace self.cFile) (← getLeanTrace)

@[inline]
def Module.mkOTarget (cTarget : FileTarget) (self : Module) : FileTarget :=
  leanOFileTarget self.oFile cTarget self.leancArgs

@[inline]
def Module.mkDynlibTarget (self : Module) (oTarget : FileTarget)
(libDirs : Array FilePath) (libTargets : Array FileTarget) : FileTarget :=
  let libsTarget : BuildTarget _ := Target.collectArray libTargets
  Target.mk self.dynlib do
    oTarget.bindAsync fun oFile oTrace => do
    libsTarget.bindSync fun libFiles libTrace => do
      buildFileUnlessUpToDate self.dynlibFile (oTrace.mix libTrace) do
        let args := #[oFile.toString] ++ libDirs.map (s!"-L{·}") ++ libFiles.map (s!"-l{·}")
        compileSharedLib self.dynlibFile args (← getLeanc)

-- # Recursive Building

section
variable [Monad m] [MonadLiftT BuildM m] [MonadBuildStore m]

/-- Build the dynlibs of the imports that want precompilation. -/
@[specialize] def recBuildPrecompileDynlibs (pkg : Package) (imports : Array Module)
: IndexT m (Array ActiveFileTarget × Array ActiveFileTarget × Array FilePath) := do
  have : MonadLift BuildM m := ⟨liftM⟩
  -- Build and collect precompiled imports
  let mut pkgs := #[]
  let mut pkgSet := PackageSet.empty.insert pkg
  let mut modTargets := #[]
  for imp in imports do
    if imp.shouldPrecompile then
      unless pkgSet.contains imp.pkg do
        pkgSet := pkgSet.insert imp.pkg
        pkgs := pkgs.push imp.pkg
      modTargets := modTargets.push <| ← imp.recBuildFacet &`lean.dynlib
  pkgs := pkgs.push pkg
  -- Compute library directories and external library targets
  let mut libDirs := #[]
  let mut pkgTargets := #[]
  for pkg in pkgs do
    libDirs := libDirs.push pkg.libDir
    let externLibTargets ← pkg.externLibs.mapM (·.recBuildShared)
    for target in externLibTargets do
      if let some parent := target.info.parent then
        libDirs := libDirs.push parent
      if let some stem := target.info.fileStem then
        if stem.startsWith "lib" then
          pkgTargets := pkgTargets.push <| target.withInfo <| stem.drop 3
        else
          logWarning s!"external library `{target.info}` was skipped because it does not start with `lib`"
      else
        logWarning s!"external library `{target.info}` was skipped because it has no file name"
  return (modTargets, pkgTargets, libDirs)

/--
Recursively build a module and its (transitive, local) imports,
optionally outputting a `.c` file as well if `c` is set to `true`.
-/
@[specialize] def Module.recBuildLean (mod : Module) (c : Bool)
: IndexT m ActiveOpaqueTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let extraDepTarget ← mod.pkg.recBuildFacet &`extraDep
  let (imports, transImports) ← mod.recBuildFacet &`lean.imports
  let (modTargets, pkgTargets, libDirs) ← recBuildPrecompileDynlibs mod.pkg transImports
   -- Note: Lean wants the external library symbols before module symbols
  let dynlibsTarget ← ActiveTarget.collectArray <| pkgTargets ++ modTargets
  let importTarget ←
    if c then
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (·.recBuildFacet &`lean.c)
    else
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (·.recBuildFacet &`lean)
  let depTarget := Target.active <| ← extraDepTarget.mixOpaqueAsync
    <| ← dynlibsTarget.mixOpaqueAsync importTarget
  let dynlibs := dynlibsTarget.info.map (FilePath.mk s!"lib{·}.{sharedLibExt}")
  let modTarget ← mod.soloTarget dynlibs libDirs.toList depTarget c |>.activate
  store (mod.mkBuildKey &`lean) modTarget
  store (mod.mkBuildKey &`olean) <| modTarget.withInfo mod.oleanFile
  store (mod.mkBuildKey &`ilean) <| modTarget.withInfo mod.ileanFile
  if c then
    let cTarget ← mod.mkCTarget (Target.active modTarget) |>.activate
    store (mod.mkBuildKey &`lean.c) cTarget
    return cTarget.withoutInfo
  else
    return modTarget

/--
Recursively parse the Lean files of a module and its imports
building an `Array` product of its direct and transitive local imports.
-/
@[specialize] def Module.recParseImports (mod : Module)
: IndexT m (Array Module × Array Module) := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let mut transImports := #[]
  let mut directImports := #[]
  let mut importSet := ModuleSet.empty
  let contents ← IO.FS.readFile mod.leanFile
  let (imports, _, _) ← Lean.Elab.parseImports contents mod.leanFile.toString
  for imp in imports do
    if let some mod ← findModule? imp.module then
      let (_, impTransImports) ← mod.recBuildFacet &`lean.imports
      for transImp in impTransImports do
        unless importSet.contains transImp do
          importSet := importSet.insert transImp
          transImports := transImports.push transImp
      unless importSet.contains mod do
        importSet := importSet.insert mod
        transImports := transImports.push mod
      directImports := directImports.push mod
  return (directImports, transImports)

/--
Recursively build the shared library of a module (e.g., for `--load-dynlib`).
-/
@[specialize] def Module.recBuildDynLib (mod : Module)
: IndexT m ActiveFileTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let oTarget := Target.active <| ← mod.recBuildFacet &`lean.o
  let (_, transImports) ← mod.recBuildFacet &`lean.imports
  let (modTargets, pkgTargets, libDirs) ← recBuildPrecompileDynlibs mod.pkg transImports
  let libTargets := modTargets ++ pkgTargets |>.map Target.active
  mod.mkDynlibTarget oTarget libDirs libTargets |>.activate
