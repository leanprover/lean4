/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Package
import Lake.Build.Targets

open System
open Lean (Name NameMap)

namespace Lake

-- # Build Package .o Files

def Package.oFileTargetsOf
(targetMap : ModuleMap ActiveOpaqueTarget) (self : Package) : Array FileTarget :=
  targetMap.fold (fun arr k v => arr.push (k, v)) #[] |>.filterMap fun (key, target) =>
    if key.facet == `lean.c && self.isLocalModule key.module then
      let mod : Module := ⟨self, key.module⟩
      let target := Target.active <| target.withInfo mod.cFile
      leanOFileTarget mod.oFile target self.moreLeancArgs
    else
      none

def Module.mkOTarget (modTarget : OpaqueTarget) (self : Module) : FileTarget :=
  leanOFileTarget self.oFile (self.mkCTarget modTarget) self.leancArgs

def Module.oTarget (self : Module) : FileTarget :=
  self.mkOTarget <| self.leanBinTarget (c := true)

-- # Build Package Static Lib

def Package.mkStaticLibTarget (self : Package) (lib : LeanLibConfig) : FileTarget :=
  let libFile := self.libDir / lib.staticLibFileName
  BuildTarget.mk' libFile do
    let depTarget ← self.buildExtraDepsTarget
    let mods ← self.getLibModuleArray lib
    let moduleTargetMap ← buildModuleMap mods $
      recBuildModuleTargetWithDeps depTarget (c := true)
    let oFileTargets := self.oFileTargetsOf moduleTargetMap
    staticLibTarget libFile oFileTargets |>.materializeAsync

protected def Package.staticLibTarget (self : Package) : FileTarget :=
  self.mkStaticLibTarget self.builtinLibConfig

-- # Build Package Shared Lib

def Package.linkTargetsOf
(targetMap : ModuleMap ActiveOpaqueTarget) (self : Package) : LakeM (Array FileTarget) := do
  let collect dep recurse := do
      let pkg := (← findPackage? dep.name).get!
      pkg.dependencies.forM fun dep => discard <| recurse dep
      return pkg.oFileTargetsOf targetMap ++ pkg.externLibTargets
  let ⟨x, map⟩ ← RBTopT.run (cmp := Name.quickCmp) <| self.dependencies.forM fun dep =>
    discard <| buildTop collect Dependency.name dep
  match x with
  | Except.ok _ =>
    let ts := map.fold (fun acc _ vs => acc ++ vs) #[]
    return self.oFileTargetsOf targetMap ++ self.externLibTargets ++ ts
  | Except.error _ => panic! "dependency cycle emerged after resolution"

def Package.mkSharedLibTarget (self : Package) (lib : LeanLibConfig) : FileTarget :=
  let libFile := self.libDir / lib.sharedLibFileName
  BuildTarget.mk' libFile do
    let depTarget ← self.buildExtraDepsTarget
    let mods ← self.getLibModuleArray lib
    let moduleTargetMap ← buildModuleMap mods $
      recBuildModuleTargetWithDeps depTarget (c := true)
    let linkTargets ← self.linkTargetsOf moduleTargetMap
    let target := leanSharedLibTarget libFile linkTargets lib.linkArgs
    target.materializeAsync

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  self.mkSharedLibTarget self.builtinLibConfig

-- # Build Package Bin

def Package.mkExeTarget (self : Package) (exe : LeanExeConfig) : FileTarget :=
  let exeFile := self.binDir / exe.fileName
  BuildTarget.mk' exeFile do
    let root : Module := ⟨self, exe.root⟩
    let depTarget ← self.buildExtraDepsTarget
    let moduleTargetMap ← buildModuleMap #[root] $
      recBuildModuleTargetWithDeps depTarget (c := true)
    let pkgLinkTargets ← self.linkTargetsOf moduleTargetMap
    let linkTargets :=
      if self.isLocalModule exe.root then
        pkgLinkTargets
      else
        let rootTarget := moduleTargetMap.find? (root.key `lean) |>.get!
        let rootLinkTarget := root.mkOTarget <| Target.active rootTarget
        #[rootLinkTarget] ++ pkgLinkTargets
    let target := leanExeTarget exeFile linkTargets exe.linkArgs
    target.materializeAsync

protected def Package.exeTarget (self : Package) : FileTarget :=
  self.mkExeTarget self.builtinExeConfig
