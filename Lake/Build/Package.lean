/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lake.Build.Module

open Std System
open Lean hiding SearchPath

namespace Lake

-- # Build Packages

/-- Build the `extraDepTarget` of all dependent packages into a single target. -/
protected def Package.buildExtraDepsTarget (self : Package) : SchedulerM ActiveOpaqueTarget := do
  let collect pkg depTargets := do
    let extraDepTarget ← pkg.extraDepTarget.activate
    let depTarget ← ActiveTarget.collectOpaqueArray depTargets
    extraDepTarget.mixOpaqueAsync depTarget
  let build dep recurse := do
    let pkg := (← findPackage? dep.name).get!
    let depTargets ← pkg.dependencies.mapM recurse
    liftM <| collect pkg depTargets
  let targetsE ← EStateT.run' (mkRBMap _ _ Name.quickCmp) <|
    self.dependencies.mapM fun dep => buildTop Dependency.name build dep
  match targetsE with
  | Except.ok targets => collect self targets
  | Except.error _ => panic! "dependency cycle emerged after resolution"

/-- Build the `extraDepTarget` of all workspace packages into a single target. -/
def buildExtraDepsTarget : SchedulerM ActiveOpaqueTarget := do
  ActiveTarget.collectOpaqueArray <| ← do
    (← getWorkspace).packageArray.mapM (·.extraDepTarget.activate)

-- # Build Package Modules

def withExtraDepTarget (depTarget : ActiveOpaqueTarget) (act : BuildT m α) : BuildT m α :=
  fun ctx => act {ctx with extraDepJob := depTarget.task}

def Package.getLibModuleArray (lib : LeanLibConfig) (self : Package) : IO (Array Module) := do
  return (← lib.getModuleArray self.srcDir).map (⟨self, WfName.ofName ·⟩)

/--
Build the `extraDepTarget` of a package and its (transitive) dependencies
and then build the target `facet` of library's modules recursively, constructing
a single opaque target for the whole build.
-/
def Package.buildLibModules
(self : Package) (lib : LeanLibConfig) (facet : WfName)
[DynamicType FacetData facet (ActiveBuildTarget α)] : SchedulerM Job := do
  withExtraDepTarget (← self.buildExtraDepsTarget) do
    let buildMods : BuildM _ := do
      let mods ← self.getLibModuleArray lib
      let modTargets ← buildModuleArray mods facet
      (·.task) <$> ActiveTarget.collectOpaqueArray modTargets
    buildMods.catchFailure fun _ => pure <| failure

def Package.mkLibTarget (self : Package) (lib : LeanLibConfig) : OpaqueTarget :=
  Target.opaque <| self.buildLibModules lib &`lean

def Package.libTarget (self : Package) : OpaqueTarget :=
  self.mkLibTarget self.builtinLibConfig

-- # Build Specific Modules of the Package

def Module.facetTarget (facet : WfName) (self : Module)
[DynamicType FacetData facet (ActiveBuildTarget α)] : OpaqueTarget :=
  BuildTarget.mk' () do
    withExtraDepTarget (← self.pkg.buildExtraDepsTarget) do
      return (← buildModule self facet).task

@[inline] def Module.oleanTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean |>.withInfo self.oleanFile

@[inline] def Module.ileanTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean  |>.withInfo self.ileanFile

@[inline] def Module.cTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean.c |>.withInfo self.cFile

@[inline] def Module.oTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean.o |>.withInfo self.oFile

-- # Build Imports

/--
Construct an `Array` of `Module`s for the workspace-local modules of
a `List` of import strings.
-/
def Workspace.processImportList
(imports : List String) (self : Workspace) : Array Module := Id.run do
  let mut localImports := #[]
  for imp in imports do
    if let some mod := self.findModule? imp.toName then
      localImports := localImports.push mod
  return localImports

/--
Build the workspace-local modules of list of imports.

Build only module `.olean` and `.ilean` files if
the default package build does not include any binary targets
Otherwise, also build `.c` files.
-/
def Package.buildImportsAndDeps (imports : List String) (self : Package) : BuildM PUnit := do
  let depTarget ← self.buildExtraDepsTarget
  if imports.isEmpty then
    -- wait for deps to finish building
    depTarget.buildOpaque
  else
    -- build local imports from list
    let mods := (← getWorkspace).processImportList imports
    if self.leanExes.isEmpty && self.defaultFacet matches .none | .leanLib | .oleans then
      let targets ← buildModuleArray mods &`lean
      targets.forM (·.buildOpaque)
    else
      let targets ← buildModuleArray mods &`lean.c
      targets.forM (·.buildOpaque)
