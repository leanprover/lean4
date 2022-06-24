/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Module

open Std System
open Lean hiding SearchPath

namespace Lake

-- # Build Package Lean Lib

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

-- # Build Package Static Lib

def Package.localTargetsOf (map : NameMap (ActiveBuildTarget α)) (self : Package) : Array (BuildTarget α) :=
  map.fold (fun a n v => if self.isLocalModule n then a.push (Target.active v) else a) #[]

def Package.mkStaticLibTarget (lib : LeanLibConfig) (self : Package) : FileTarget :=
  let libFile := self.libDir / lib.staticLibFileName
  BuildTarget.mk' libFile do
    let mods ← self.getLibModuleArray lib
    let oFileTargets := self.localTargetsOf <| ← buildModuleFacetMap mods &`lean.o
    staticLibTarget libFile oFileTargets |>.materializeAsync

protected def Package.staticLibTarget (self : Package) : FileTarget :=
  self.mkStaticLibTarget self.builtinLibConfig

-- # Build Package Shared Lib

def Package.linkTargetsOf
(targetMap : NameMap ActiveFileTarget) (self : Package) : LakeM (Array FileTarget) := do
  let collect dep recurse := do
    let pkg := (← findPackage? dep.name).get!
    pkg.dependencies.forM fun dep => discard <| recurse dep
    return pkg.localTargetsOf targetMap ++ pkg.externLibTargets
  let ⟨x, map⟩ ← EStateT.run (mkRBMap _ _ Name.quickCmp) <|
    self.dependencies.forM fun dep => discard <| buildTop Dependency.name collect dep
  match x with
  | Except.ok _ =>
    let ts := map.fold (fun acc _ vs => acc ++ vs) #[]
    return self.localTargetsOf targetMap ++ self.externLibTargets ++ ts
  | Except.error _ => panic! "dependency cycle emerged after resolution"

def Package.mkSharedLibTarget (self : Package) (lib : LeanLibConfig) : FileTarget :=
  let libFile := self.libDir / lib.sharedLibFileName
  BuildTarget.mk' libFile do
    let mods ← self.getLibModuleArray lib
    let linkTargets ← self.linkTargetsOf <| ← buildModuleFacetMap mods &`lean.o
    let target := leanSharedLibTarget libFile linkTargets lib.linkArgs
    target.materializeAsync

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  self.mkSharedLibTarget self.builtinLibConfig
