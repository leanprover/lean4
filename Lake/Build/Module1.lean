/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Elab.Import
import Lake.Build.Info
import Lake.Build.Store
import Lake.Build.Targets

open Std System
open Lean hiding SearchPath

namespace Lake

abbrev ModuleSet := RBTree Module (·.name.quickCmp ·.name)
@[inline] def ModuleSet.empty : ModuleSet := RBTree.empty

abbrev ModuleMap (α) := RBMap Module α (·.name.quickCmp ·.name)
@[inline] def ModuleMap.empty : ModuleMap α := RBMap.empty

-- # Solo Module Targets

def Module.soloTarget (mod : Module)
(dynlibs : Array FilePath) (depTarget : BuildTarget x) (c := true) : OpaqueTarget :=
  Target.opaque <| depTarget.bindOpaqueSync fun depTrace => do
    let argTrace : BuildTrace := pureHash mod.leanArgs
    let srcTrace : BuildTrace ← computeTrace mod.leanFile
    let modTrace := (← getLeanTrace).mix <| argTrace.mix <| srcTrace.mix depTrace
    let modUpToDate ← modTrace.checkAgainstFile mod mod.traceFile
    if c then
      let cUpToDate ← modTrace.checkAgainstFile mod.cFile mod.cTraceFile
      unless modUpToDate && cUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile mod.cFile
          (← getOleanPath) mod.pkg.rootDir dynlibs mod.leanArgs (← getLean)
      modTrace.writeToFile mod.cTraceFile
    else
      unless modUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile none
          (← getOleanPath) mod.pkg.rootDir dynlibs mod.leanArgs (← getLean)
    modTrace.writeToFile mod.traceFile
    return depTrace

def Module.mkCTarget (modTarget : BuildTarget x) (self : Module) : FileTarget :=
  Target.mk self.cFile <| modTarget.bindOpaqueSync fun _ =>
    return mixTrace (← computeTrace self.cFile) (← getLeanTrace)

@[inline]
def Module.mkOTarget (cTarget : FileTarget) (self : Module) : FileTarget :=
  leanOFileTarget self.oFile cTarget self.leancArgs

@[inline]
def Module.mkDynlibTarget (linkTargets : Array FileTarget) (self : Module) : FileTarget :=
  leanSharedLibTarget self.dynlib linkTargets self.linkArgs

-- # Recursive Building

section
variable [Monad m] [MonadLiftT BuildM m] [MonadBuildStore m]

/-- Build the dynlibs of the imports that want precompilation. -/
@[specialize] def recBuildPrecompileDynlibs (imports : Array Module)
: IndexT m (Array ActiveFileTarget) := do
  imports.filterMapM fun imp => do
    if imp.shouldPrecompile then
      return some <| ← imp.recBuildFacet &`lean.dynlib
    else
      return none

/--
Recursively build a module and its (transitive, local) imports,
optionally outputting a `.c` file as well if `c` is set to `true`.
-/
@[specialize] def Module.recBuildLean (mod : Module) (c : Bool)
: IndexT m ActiveOpaqueTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let extraDepTarget ← mod.pkg.recBuildFacet &`extraDep
  let (imports, transImports) ← mod.recBuildFacet &`lean.imports
  let dynlibsTarget ← ActiveTarget.collectArray
    <| ← recBuildPrecompileDynlibs transImports
  let importTarget ←
    if c then
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (·.recBuildFacet &`lean.c)
    else
      ActiveTarget.collectOpaqueArray
        <| ← imports.mapM (·.recBuildFacet &`lean)
  let depTarget := Target.active <| ← extraDepTarget.mixOpaqueAsync
    <| ← dynlibsTarget.mixOpaqueAsync importTarget
  let modTarget ← mod.soloTarget dynlibsTarget.info depTarget c |>.activate
  store (mod.mkBuildKey &`lean) modTarget
  store (mod.mkBuildKey &`olean) modTarget
  store (mod.mkBuildKey &`ilean) modTarget
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
  let contents ← IO.FS.readFile mod.leanFile
  let (imports, _, _) ← Elab.parseImports contents mod.leanFile.toString
  let importSet ← imports.foldlM (init := ModuleSet.empty) fun a imp => do
    if let some mod ← findModule? imp.module then return a.insert mod else return a
  let mut imports := #[]
  let mut transImports := ModuleSet.empty
  for imp in importSet do
    let (_, impTransImports) ← imp.recBuildFacet &`lean.imports
    for imp in impTransImports do
      transImports := transImports.insert imp
    transImports := transImports.insert imp
    imports := imports.push imp
  return (imports, transImports.toArray)

/--
Recursively build the shared library of a module (e.g., for `--load-dynlib`).
-/
@[specialize] def Module.recBuildDynLib (mod : Module)
: IndexT m ActiveFileTarget := do
  have : MonadLift BuildM m := ⟨liftM⟩
  let oTarget ← mod.recBuildFacet &`lean.o
  let (_, transImports) ← mod.recBuildFacet &`lean.imports
  let dynlibTargets ← recBuildPrecompileDynlibs transImports
  -- TODO: Link in external libraries
  -- let externLibTargets ← mod.pkg.externLibTargets.mapM (·.activate)
  -- let linkTargets := #[oTarget] ++ sharedLibTargets ++ externLibTargets |>.map Target.active
  let linkTargets := #[oTarget] ++ dynlibTargets |>.map Target.active
  mod.mkDynlibTarget linkTargets |>.activate
