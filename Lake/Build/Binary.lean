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

def Package.oFileTargetOf
(mod : Name) (target : ActiveOleanAndCTarget) (self : Package) : FileTarget :=
  let oFile := self.modToO mod
  let cTarget := Target.active <| ActiveOleanAndCTarget.cTarget target
  leanOFileTarget oFile cTarget self.moreLeancArgs

def Package.oFileTargetsOf
(targetMap : NameMap ActiveOleanAndCTarget) (self : Package) : Array FileTarget :=
  targetMap.fold (fun arr k v => arr.push (k, v)) #[] |>.filterMap fun (mod, target) =>
    if self.isLocalModule mod then self.oFileTargetOf mod target else none

def Package.moduleOTarget (mod : Name) (self : Package) : FileTarget :=
  let oFile := self.modToO mod
  let cTarget := self.moduleOleanAndCTarget mod |>.cTarget
  leanOFileTarget oFile cTarget self.moreLeancArgs

-- # Build Package Static Lib

def Package.mkStaticLibTarget (self : Package) (lib : LeanLibConfig) : FileTarget :=
  let libFile := self.libDir / lib.staticLibFileName
  BuildTarget.mk' libFile do
    let depTarget ← self.buildExtraDepsTarget
    let infos := (← lib.getModuleArray self.srcDir).map (Module.mk self)
    let moduleTargetMap ← buildModuleMap infos $
      recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let oFileTargets := self.oFileTargetsOf moduleTargetMap
    staticLibTarget libFile oFileTargets |>.materializeAsync

protected def Package.staticLibTarget (self : Package) : FileTarget :=
  self.mkStaticLibTarget self.builtinLibConfig

def Package.staticLibTargets (self : Package) : Array FileTarget :=
  #[self.staticLibTarget] ++ self.moreLibTargets

-- # Build Package Shared Lib

def Package.linkTargetsOf
(targetMap : NameMap ActiveOleanAndCTarget) (self : Package) : LakeM (Array FileTarget) := do
  let collect dep recurse := do
      let pkg := (← getPackageByName? dep.name).get!
      pkg.dependencies.forM fun dep => discard <| recurse dep
      return pkg.oFileTargetsOf targetMap ++ pkg.moreLibTargets
  let ⟨x, map⟩ ← RBTopT.run <| self.dependencies.forM fun dep =>
    discard <| buildRBTop (cmp := Name.quickCmp) collect Dependency.name dep
  match x with
  | Except.ok _ =>
    let ts := map.fold (fun acc _ vs => acc ++ vs) #[]
    return self.oFileTargetsOf targetMap ++ self.moreLibTargets ++ ts
  | Except.error _ => panic! "dependency cycle emerged after resolution"

def Package.mkSharedLibTarget (self : Package) (lib : LeanLibConfig) : FileTarget :=
  let libFile := self.libDir / lib.sharedLibFileName
  BuildTarget.mk' libFile do
    let depTarget ← self.buildExtraDepsTarget
    let infos := (← lib.getModuleArray self.srcDir).map (Module.mk self)
    let moduleTargetMap ← buildModuleMap infos $
      recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let linkTargets ← self.linkTargetsOf moduleTargetMap
    let target := leanSharedLibTarget libFile linkTargets lib.linkArgs
    target.materializeAsync

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  self.mkSharedLibTarget self.builtinLibConfig

-- # Build Package Bin

def Package.mkExeTarget (self : Package) (exe : LeanExeConfig) : FileTarget :=
  let exeFile := self.binDir / exe.fileName
  BuildTarget.mk' exeFile do
    let depTarget ← self.buildExtraDepsTarget
    let moduleTargetMap ← buildModuleMap #[⟨self, exe.root⟩] $
      recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let pkgLinkTargets ← self.linkTargetsOf moduleTargetMap
    let linkTargets :=
      if self.isLocalModule exe.root then
        pkgLinkTargets
      else
        let rootTarget := moduleTargetMap.find? exe.root |>.get!
        let rootLinkTarget := self.oFileTargetOf exe.root rootTarget
        #[rootLinkTarget] ++ pkgLinkTargets
    let target := leanBinTarget exeFile linkTargets exe.linkArgs
    target.materializeAsync

protected def Package.exeTarget (self : Package) : FileTarget :=
  self.mkExeTarget self.builtinExeConfig
