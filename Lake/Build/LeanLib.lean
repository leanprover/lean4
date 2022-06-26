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

def LeanLib.localTargetsOf (map : NameMap (ActiveBuildTarget α)) (self : LeanLib) : Array (BuildTarget α) :=
  map.fold (fun a n v => if self.isLocalModule n then a.push (Target.active v) else a) #[]

protected def LeanLib.staticLibTarget (self : LeanLib) : FileTarget :=
  BuildTarget.mk' self.staticLibFile do
    let mods ← self.getModuleArray
    let oFileTargets := self.localTargetsOf <| ← buildModuleFacetMap mods &`lean.o
    staticLibTarget self.staticLibFile oFileTargets |>.materializeAsync

protected def Package.staticLibTarget (self : Package) : FileTarget :=
  self.builtinLib.staticLibTarget

-- # Build Shared Lib

def Package.localTargetsOf (map : NameMap (ActiveBuildTarget α)) (self : Package) : Array (BuildTarget α) :=
  map.fold (fun a n v => if self.isLocalModule n then a.push (Target.active v) else a) #[]

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

protected def LeanLib.sharedLibTarget (self : LeanLib) : FileTarget :=
  BuildTarget.mk' self.sharedLibFile do
    let mods ← self.getModuleArray
    let linkTargets ← self.pkg.linkTargetsOf <| ← buildModuleFacetMap mods &`lean.o
    let target := leanSharedLibTarget self.sharedLibFile linkTargets self.linkArgs
    target.materializeAsync

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  self.builtinLib.sharedLibTarget
