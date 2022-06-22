/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Package
import Lake.Build.Targets

open Std System
open Lean (Name NameMap)

namespace Lake

-- # Build Package Static Lib

def Package.localTargetsOf (map : NameMap (ActiveBuildTarget α)) (self : Package) : Array (BuildTarget α) :=
  map.fold (fun a n v => if self.isLocalModule n then a.push (Target.active v) else a) #[]

def Package.mkStaticLibTarget (lib : LeanLibConfig) (self : Package) : FileTarget :=
  let libFile := self.libDir / lib.staticLibFileName
  BuildTarget.mk' libFile do
    withExtraDepTarget (← self.buildExtraDepsTarget) do
      let mods ← self.getLibModuleArray lib
      let oFileTargets := self.localTargetsOf <| ← buildModuleMap mods &`lean.o
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
    withExtraDepTarget (← self.buildExtraDepsTarget) do
      let mods ← self.getLibModuleArray lib
      let linkTargets ← self.linkTargetsOf <| ← buildModuleMap mods &`lean.o
      let target := leanSharedLibTarget libFile linkTargets lib.linkArgs
      target.materializeAsync

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  self.mkSharedLibTarget self.builtinLibConfig

-- # Build Package Bin

def Package.mkExeTarget (self : Package) (exe : LeanExeConfig) : FileTarget :=
  let exeFile := self.binDir / exe.fileName
  BuildTarget.mk' exeFile do
    let root : Module := ⟨self, WfName.ofName exe.root⟩
    withExtraDepTarget (← self.buildExtraDepsTarget) do
      let cTargetMap ← buildModuleMap #[root] &`lean.c
      let pkgLinkTargets ← self.linkTargetsOf cTargetMap
      let linkTargets :=
        if self.isLocalModule exe.root then
          pkgLinkTargets
        else
          let rootTarget := cTargetMap.find? root.name |>.get!
          let rootLinkTarget := root.mkOTarget <| Target.active rootTarget
          #[rootLinkTarget] ++ pkgLinkTargets
      let target := leanExeTarget exeFile linkTargets exe.linkArgs
      target.materializeAsync

protected def Package.exeTarget (self : Package) : FileTarget :=
  self.mkExeTarget self.builtinExeConfig
