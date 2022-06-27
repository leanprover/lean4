/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Module

open Std System
open Lean hiding SearchPath

namespace Lake

-- # Build Lean Lib

/--
Build the `extraDepTarget` of a package and its (transitive) dependencies
and then build the target `facet` of library's modules recursively, constructing
a single opaque target for the whole build.
-/
def LeanLib.buildModules (self : LeanLib) (facet : WfName)
[DynamicType ModuleData facet (ActiveBuildTarget α)] : SchedulerM Job := do
  let buildMods : BuildM _ := do
    let mods ← self.getModuleArray
    let modTargets ← buildModuleFacetArray mods facet
    (·.task) <$> ActiveTarget.collectOpaqueArray modTargets
  buildMods.catchFailure fun _ => pure <| failure

def LeanLib.leanTarget (self : LeanLib) : OpaqueTarget :=
  Target.opaque <| self.buildModules &`lean

def Package.libTarget (self : Package) : OpaqueTarget :=
  self.builtinLib.leanTarget

-- # Build Static Lib

def LeanLib.buildStatic (self : LeanLib) : BuildM ActiveFileTarget := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty do
    have of_data := by unfold BuildData, BuildInfo.key; simp; rfl
    cast of_data <| buildIndexTop <| BuildInfo.staticLeanLib self

protected def LeanLib.staticLibTarget (self : LeanLib) : FileTarget :=
  BuildTarget.mk' self.staticLibFile do self.buildStatic <&> (·.task)

protected def Package.staticLibTarget (self : Package) : FileTarget :=
  self.builtinLib.staticLibTarget

-- # Build Shared Lib

def LeanLib.buildShared (self : LeanLib) : BuildM ActiveFileTarget := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty do
    have of_data := by unfold BuildData, BuildInfo.key; simp; rfl
    cast of_data <| buildIndexTop <| BuildInfo.sharedLeanLib self

protected def LeanLib.sharedLibTarget (self : LeanLib) : FileTarget :=
  BuildTarget.mk' self.sharedLibFile do self.buildShared <&> (·.task)

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  self.builtinLib.sharedLibTarget

-- # Build Executable

def LeanExe.build (self : LeanExe) : BuildM ActiveFileTarget := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty do
    have of_data := by unfold BuildData, BuildInfo.key; simp; rfl
    cast of_data <| buildIndexTop <| BuildInfo.leanExe self

def LeanExe.target (self : LeanExe) : FileTarget :=
  BuildTarget.mk' self.file do self.build <&> (·.task)

protected def Package.exeTarget (self : Package) : FileTarget :=
  self.builtinExe.target
