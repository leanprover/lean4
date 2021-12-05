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

protected def Package.staticLibTarget (self : Package) : FileTarget :=
 Target.mk self.staticLibFile do
    let depTarget ← self.buildExtraDepsTarget
    let moduleTargetMap ← buildModuleTargetMap (← self.getModuleArray) $
      recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let oFileTargets := self.oFileTargetsOf moduleTargetMap
    staticLibTarget self.staticLibFile oFileTargets |>.materializeAsync

def Package.buildStaticLib (self : Package) : BuildM FilePath :=
  self.staticLibTarget.build

def Package.staticLibTargets (self : Package) : Array FileTarget :=
  #[self.staticLibTarget] ++ self.moreLibTargets

-- # Build Package Shared Lib

def Package.linkTargetsOf
(targetMap : NameMap ActiveOleanAndCTarget) (self : Package) : BuildM (Array FileTarget) := do
  let collect dep recurse := do
      let pkg := (← getPackageByName? dep.name).get!
      let depTargets ← pkg.dependencies.concatMapM recurse
      return pkg.oFileTargetsOf targetMap ++ pkg.moreLibTargets ++ depTargets
  let depLinkTargets ← failOnBuildCycle <| ← RBTopT.run' <| self.dependencies.concatMapM fun dep =>
    buildRBTop (cmp := Name.quickCmp) collect Dependency.name dep
  return self.oFileTargetsOf targetMap ++ self.moreLibTargets ++ depLinkTargets

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  Target.mk self.sharedLibFile do
    let depTarget ← self.buildExtraDepsTarget
    let moduleTargetMap ← buildModuleTargetMap (← self.getModuleArray) $
      recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let linkTargets ← self.linkTargetsOf moduleTargetMap
    let target := leanSharedLibTarget self.sharedLibFile linkTargets self.moreLinkArgs
    target.materializeAsync

def Package.buildSharedLib (self : Package) : BuildM FilePath :=
  self.sharedLibTarget.build

-- # Build Package Bin

protected def Package.binTarget (self : Package) : FileTarget :=
  Target.mk self.binFile do
    let depTarget ← self.buildExtraDepsTarget
    let moduleTargetMap ← buildModuleTargetMap #[self.binRoot] $
      recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let pkgLinkTargets ← self.linkTargetsOf moduleTargetMap
    let linkTargets :=
      if self.isLocalModule self.binRoot then
        pkgLinkTargets
      else
        let rootTarget := moduleTargetMap.find? self.binRoot |>.get!
        let rootLinkTarget := self.oFileTargetOf self.binRoot rootTarget
        #[rootLinkTarget] ++ pkgLinkTargets
    let target := leanBinTarget self.binFile linkTargets self.moreLinkArgs
    target.materializeAsync

def Package.buildBin (self : Package) : BuildM FilePath :=
  self.binTarget.build
