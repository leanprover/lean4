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

-- # Build Package Modules



def Package.getLibModuleArray (lib : LeanLibConfig) (self : Package) : IO (Array Module) := do
  return (← lib.getModuleArray self.srcDir).map (⟨self, WfName.ofName ·⟩)

/--
Build the `extraDepTarget` of a package and its (transitive) dependencies
and then build the target `facet` of library's modules recursively, constructing
a single opaque target for the whole build.
-/
def Package.buildLibModules
(self : Package) (lib : LeanLibConfig) (facet : WfName)
[DynamicType ModuleData facet (ActiveBuildTarget α)] : SchedulerM Job := do
  let buildMods : BuildM _ := do
    let mods ← self.getLibModuleArray lib
    let modTargets ← buildModuleFacetArray mods facet
    (·.task) <$> ActiveTarget.collectOpaqueArray modTargets
  buildMods.catchFailure fun _ => pure <| failure

def Package.mkLibTarget (self : Package) (lib : LeanLibConfig) : OpaqueTarget :=
  Target.opaque <| self.buildLibModules lib &`lean

def Package.libTarget (self : Package) : OpaqueTarget :=
  self.mkLibTarget self.builtinLibConfig

-- # Build Specific Modules of the Package

def Module.facetTarget (facet : WfName) (self : Module)
[DynamicType ModuleData facet (ActiveBuildTarget α)] : OpaqueTarget :=
  BuildTarget.mk' () do return (← buildModuleFacet self facet).task

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
  if imports.isEmpty then
    -- build the package's (and its dependencies') `extraDepTarget`
    buildPackageFacet self &`extraDep >>= (·.buildOpaque)
  else
    -- build local imports from list
    let mods := (← getWorkspace).processImportList imports
    if self.leanExes.isEmpty && self.defaultFacet matches .none | .leanLib | .oleans then
      let targets ← buildModuleFacetArray mods &`lean
      targets.forM (·.buildOpaque)
    else
      let targets ← buildModuleFacetArray mods &`lean.c
      targets.forM (·.buildOpaque)
