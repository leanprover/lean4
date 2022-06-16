/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Build.Target
import Lake.Build.Actions
import Lake.Build.Recursive
import Lake.Build.TargetTypes
import Lake.Config.Module

open System
open Lean hiding SearchPath

namespace Lake

-- # Build Key

structure ModuleBuildKey where
  module : Name
  facet : Name
  deriving Inhabited, Repr, BEq, Hashable

namespace ModuleBuildKey

def quickCmp (lhs rhs : ModuleBuildKey) :=
  match lhs.module.quickCmp rhs.module with
  | .eq => lhs.facet.quickCmp rhs.facet
  | ord => ord

protected def toString (self : ModuleBuildKey) :=
  s!"{self.module}:{self.facet}"

instance : ToString ModuleBuildKey := ⟨(·.toString)⟩

end ModuleBuildKey

def Module.key (facet : Name) (self : Module) : ModuleBuildKey :=
  ⟨self.name, facet⟩

-- # Single Module Target

def moduleTarget (mod : Module)
(depTarget : BuildTarget x) (c := true) : OpaqueTarget :=
  Target.opaque <| depTarget.bindOpaqueSync fun depTrace => do
    let argTrace : BuildTrace := pureHash mod.leanArgs
    let srcTrace : BuildTrace ← computeTrace mod.leanFile
    let modTrace := (← getLeanTrace).mix <| argTrace.mix <| srcTrace.mix depTrace
    let modUpToDate ← modTrace.checkAgainstFile mod mod.traceFile
    if c then
      let cUpToDate ← modTrace.checkAgainstFile mod.cFile mod.cTraceFile
      unless modUpToDate && cUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile mod.cFile
          (← getOleanPath) mod.pkg.rootDir mod.leanArgs (← getLean)
      modTrace.writeToFile mod.cTraceFile
    else
      unless modUpToDate do
        compileLeanModule mod.leanFile mod.oleanFile mod.ileanFile none
          (← getOleanPath) mod.pkg.rootDir mod.leanArgs (← getLean)
    modTrace.writeToFile mod.traceFile
    return depTrace

-- # Recursive Building

/--
Produces a recursive module target builder that builds the target module
with the `build` function after recursively building its local imports
(relative to the workspace).
-/
def recBuildModuleWithLocalImports [Monad m] [MonadLiftT BuildM m]
(build : Module → List α → m α) : RecBuild Module α m := fun mod recurse => do
  have : MonadLift BuildM m := ⟨liftM⟩
  let contents ← IO.FS.readFile mod.leanFile
  let (imports, _, _) ← Elab.parseImports contents mod.leanFile.toString
  -- we construct the import targets even if a rebuild is not required
  -- because other build processes (ex. `.o`) rely on the map being complete
  let importTargets ← imports.filterMapM fun imp => OptionT.run do
    recurse <| ← OptionT.mk <| findModule? imp.module
  build mod importTargets

/--
Produces a recursive module target builder that builds the
`olean`, `ilean`, and (optionally) `c` files of a module and its local imports
after `extraDepTarget` finishes building.
-/
def recBuildModuleTargetWithDeps
[Monad m] [MonadLiftT BuildM m] [MonadStore ModuleBuildKey ActiveOpaqueTarget m]
(extraDepTarget : ActiveBuildTarget x) (c := true) : RecBuild Module ActiveOpaqueTarget m :=
  recBuildModuleWithLocalImports fun mod importTargets => do
    have : MonadLift BuildM m := ⟨liftM⟩
    let importTarget ← ActiveTarget.collectOpaqueList importTargets
    let allDepsTarget := Target.active <| ← extraDepTarget.mixOpaqueAsync importTarget
    let modTarget := (← moduleTarget mod allDepsTarget c |>.activate).withoutInfo
    if c then
      let cTarget ← liftM (m := SchedulerM) do
        return ActiveTarget.opaque <| ← modTarget.bindOpaqueSync (m := BuildM) fun _ => do
          return mixTrace (← computeTrace mod.cFile) (← getLeanTrace)
      store (mod.key `lean.c) cTarget
    return modTarget

-- ## Definitions

abbrev ModuleMap (α) :=
  Std.RBMap ModuleBuildKey α ModuleBuildKey.quickCmp

abbrev ModuleBuildM (α) :=
  -- equivalent to `RBTopT ModuleBuildKey α BuildM ModuleBuildKey.quickCmp`
  -- phrased this way to use `ModuleMap`
  EStateT (List ModuleBuildKey) (ModuleMap α) BuildM

abbrev RecModuleBuild (o) :=
  RecBuild Module o (ModuleBuildM o)

abbrev RecModuleTargetBuild :=
  RecModuleBuild ActiveOpaqueTarget

-- ## Multi-Module Builders

/-- Build a single module using the recursive module build function `build`. -/
def buildModule (mod : Module)
[Inhabited o] (build : RecModuleBuild o) : BuildM o := do
  failOnBuildCycle <| ← RBTopT.run' do
    buildTop build (·.key `lean) mod

/--
Build each module using the recursive module function `build`,
constructing an `Array`  of the results.
-/
def buildModuleArray (mods : Array Module)
[Inhabited o] (build : RecModuleBuild o) : BuildM (Array o) := do
  failOnBuildCycle <| ← RBTopT.run' <| mods.mapM <|
    buildTop build (·.key `lean)

/--
Build each module using the recursive module function `build`,
constructing a module-target `NameMap`  of the results.
-/
def buildModuleMap  (mods : Array Module)
[Inhabited o] (build : RecModuleBuild o) : BuildM (ModuleMap o) := do
  let (x, map) ← RBTopT.run <| mods.forM fun mod =>
    discard <| buildTop build (·.key `lean) mod
  failOnBuildCycle x
  return map
