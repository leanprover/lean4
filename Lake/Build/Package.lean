/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Config.Package
import Lake.Build.Module

open System
open Lean hiding SearchPath

namespace Lake

-- # Build Packages

/-- Build the `extraDepTarget` of all dependent packages into a single target. -/
protected def Package.buildExtraDepsTarget (self : Package) : BuildM ActiveOpaqueTarget := do
  let collect pkg depTargets := do
    let extraDepTarget ← self.extraDepTarget.run
    let depTarget ← ActiveTarget.collectOpaqueArray depTargets
    extraDepTarget.mixOpaqueAsync depTarget
  let build dep recurse := do
    let pkg := (← getPackageByName? dep.name).get!
    let depTargets ← pkg.dependencies.mapM recurse
    liftM <| collect pkg depTargets
  let targets ← failOnBuildCycle <| ← RBTopT.run' <| self.dependencies.mapM fun dep =>
    buildRBTop (cmp := Name.quickCmp) build Dependency.name dep
  collect self targets

/-- Build the `extraDepTarget` of all workspace packages into a single target. -/
def buildExtraDepsTarget : BuildM ActiveOpaqueTarget := do
  ActiveTarget.collectOpaqueArray <| ← do
    (← getWorkspace).packageArray.mapM (·.extraDepTarget.run)

/--
Build each module and using the given recursive module build function,
constructing a module-target `NameMap`  of the results.
-/
def buildModuleTargetMap [Inhabited i]
(mods : Array Name) (build : RecModuleTargetBuild i)
: BuildM (NameMap (ActiveBuildTarget i)) := do
  let (x, targetMap) ← RBTopT.run do
    mods.forM fun mod => discard <| buildRBTop build id mod
  failOnBuildCycle x
  return targetMap

/--
Build each module and using the given recursive module build function,
constructing a single opaque target for the whole build.
-/
def buildModulesTarget [Inhabited i] (mods : Array Name)
(build : RecModuleTargetBuild i) : BuildM ActiveOpaqueTarget := do
  failOnBuildCycle <| ← RBTopT.run' do
    let targets ← mods.mapM fun mod =>
      (·.withoutInfo) <$> buildRBTop build id mod
    ActiveTarget.collectOpaqueArray targets

-- # Build Package Modules

/-- Build the `.olean` and files of package and its dependencies' modules. -/
def Package.buildOleanTarget (self : Package) : BuildM ActiveOpaqueTarget := do
  let depTarget ← self.buildExtraDepsTarget
  buildModulesTarget (← self.getModuleArray) <|
    recBuildModuleOleanTargetWithLocalImports depTarget

/-- Build the `.olean` and `.c` files of package and its dependencies' modules. -/
def Package.buildOleanAndCTarget (self : Package) : BuildM ActiveOpaqueTarget := do
  let depTarget ← self.buildExtraDepsTarget
  buildModulesTarget (← self.getModuleArray) <|
    recBuildModuleOleanAndCTargetWithLocalImports depTarget

def Package.buildDepOleans (self : Package) : BuildM PUnit := do
  let targets ← self.dependencies.mapM fun dep => do
    (← getPackageForModule? dep.name).get!.buildOleanTarget
  targets.forM fun target => discard <| target.materialize

def Package.oleanTarget (self : Package) : OpaqueTarget :=
  Target.opaque do pure (← self.buildOleanTarget).task

def Package.build (self : Package) : BuildM PUnit := do
  discard (← self.buildOleanTarget).materialize

-- # Build Specific Modules of the Package

def Package.moduleOleanTarget (mod : Name) (self : Package) : FileTarget :=
  Target.mk (self.modToOlean mod) do
    let depTarget ← self.buildExtraDepsTarget
    let build := recBuildModuleOleanTargetWithLocalImports depTarget
    return (← buildModule mod build).task

def Package.moduleOleanAndCTarget (mod : Name) (self : Package) : OleanAndCTarget :=
  Target.mk ⟨self.modToOlean mod, self.modToC mod⟩ do
    let depTarget ← self.buildExtraDepsTarget
    let build := recBuildModuleOleanAndCTargetWithLocalImports depTarget
    return (← buildModule mod build).task

-- # Build Imports

/-- Pick the local imports of the workspace from a list of import strings. -/
def Workspace.filterLocalImports
(imports : List String) (self : Workspace) : Array Name := Id.run <| do
  let mut localImports := #[]
  for imp in imports do
    let impName := imp.toName
    if self.isLocalModule impName then
      localImports := localImports.push impName
  return localImports

/--
Build the workspace-local modules of list of imports.

Builds only module `.olean` files if the default package facet is
just `oleans`. Otherwise, builds both `.olean` and `.c` files.
-/
def buildImportsAndDeps (imports : List String := []) : BuildM PUnit := do
  let depTarget ← buildExtraDepsTarget
  if imports.isEmpty then
    -- wait for deps to finish building
    depTarget.build
  else
    -- build local imports from list
    let localImports := (← getWorkspace).filterLocalImports imports
    if (← getPackage).defaultFacet == PackageFacet.oleans then
      let build := recBuildModuleOleanTargetWithLocalImports depTarget
      let targets ← buildModules localImports build
      targets.forM (·.build)
    else
      let build := recBuildModuleOleanAndCTargetWithLocalImports depTarget
      let targets ← buildModules localImports build
      targets.forM (·.build)
