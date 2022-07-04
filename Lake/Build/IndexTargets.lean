/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index

open Std System
open Lean hiding SearchPath

namespace Lake

-- # Module Facet Targets

@[inline] def Module.facetTarget (facet : WfName) (self : Module)
[FamilyDef ModuleData facet (ActiveBuildTarget α)] : OpaqueTarget :=
  self.facet facet |>.target

@[inline] def Module.oleanTarget (self : Module) : FileTarget :=
  self.facetTarget oleanFacet |>.withInfo self.oleanFile

@[inline] def Module.ileanTarget (self : Module) : FileTarget :=
  self.facetTarget ileanFacet |>.withInfo self.ileanFile

@[inline] def Module.cTarget (self : Module) : FileTarget :=
  self.facetTarget cFacet |>.withInfo self.cFile

@[inline] def Module.oTarget (self : Module) : FileTarget :=
  self.facetTarget oFacet |>.withInfo self.oFile

-- # Pure Lean Lib Targets

/--
Build the `extraDepTarget` of a package and its (transitive) dependencies
and then build the target `facet` of library's modules recursively, constructing
a single opaque target for the whole build.
-/
def LeanLib.buildModules (self : LeanLib) (facet : WfName)
[FamilyDef ModuleData facet (ActiveBuildTarget α)] : SchedulerM Job := do
  let buildMods : BuildM _ := do
    let mods ← self.getModuleArray
    let modTargets ← failOnBuildCycle <| ← EStateT.run' BuildStore.empty
      <| mods.mapM fun mod => buildIndexTop <| mod.facet facet
    (·.task) <$> ActiveTarget.collectOpaqueArray modTargets
  buildMods.catchFailure fun _ => pure <| failure

@[inline] protected def LeanLib.leanTarget (self : LeanLib) : OpaqueTarget :=
  Target.opaque <| self.buildModules Module.leanBinFacet

@[inline] protected def Package.leanLibTarget (self : Package) : OpaqueTarget :=
  self.builtinLib.leanTarget

-- # Native Lean Lib Targets

@[inline] protected def LeanLib.staticLibTarget (self : LeanLib) : FileTarget :=
  self.static.target.withInfo self.sharedLibFile

@[inline] protected def Package.staticLibTarget (self : Package) : FileTarget :=
  self.builtinLib.staticLibTarget

@[inline] protected def LeanLib.sharedLibTarget (self : LeanLib) : FileTarget :=
  self.shared.target.withInfo self.sharedLibFile

@[inline] protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  self.builtinLib.sharedLibTarget

-- # Lean Executable Targets

@[inline] protected def LeanExe.build (self : LeanExe) : BuildM ActiveFileTarget :=
  self.info.build

@[inline] protected def LeanExe.target (self : LeanExe) : FileTarget :=
  self.info.target.withInfo self.file

@[inline] protected def Package.exeTarget (self : Package) : FileTarget :=
  self.builtinExe.target
