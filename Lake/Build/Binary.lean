/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Package
import Lake.Build.Targets

open System
open Lean (Name)

namespace Lake

-- # Build Package .o Files

def ActivePackageTarget.oFileTargets
(self : ActivePackageTarget ActiveOleanAndCTargets) : Array FileTarget :=
  self.moduleTargets.map fun (mod, target) =>
    let oFile := self.package.modToO mod
    let cTarget := Target.active <| ActiveOleanAndCTarget.cTarget target
    leanOFileTarget oFile cTarget self.package.moreLeancArgs

def Package.moduleOTarget (mod : Name) (self : Package) : FileTarget :=
  let oFile := self.modToO mod
  let cTarget := self.moduleOleanAndCTarget mod |>.cTarget
  leanOFileTarget oFile cTarget self.moreLeancArgs

-- # Build Package Static Lib

protected def ActivePackageTarget.staticLibTarget (self : ActivePackageTarget ActiveOleanAndCTargets) : FileTarget :=
  staticLibTarget self.package.staticLibFile self.oFileTargets

def ActivePackageTarget.staticLibTargets (self : ActivePackageTarget ActiveOleanAndCTargets) : Array FileTarget :=
  #[self.staticLibTarget] ++ self.package.moreLibTargets

protected def Package.staticLibTarget (self : Package) : FileTarget :=
 Target.mk self.staticLibFile do
    (← self.buildOleanAndCTarget).staticLibTarget.materializeAsync

def Package.buildStaticLib (self : Package) : BuildM FilePath :=
  self.staticLibTarget.build

-- # Build Package Shared Lib

protected def Package.sharedLibTarget (self : Package) : FileTarget :=
  Target.mk self.sharedLibFile do
    let depTargets ← self.buildDepTargets buildOleanAndCTargetWithDepTargets
    let depTarget ← self.buildDepTargetWith depTargets
    let build := self.recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let pkgTarget ← self.buildTarget build
    let linkTargets :=
      pkgTarget.oFileTargets ++ self.moreLibTargets ++
      depTargets.concatMap (·.staticLibTargets)
    let target := leanSharedLibTarget self.sharedLibFile linkTargets
    target.materializeAsync

def Package.buildSharedLib (self : Package) : BuildM FilePath :=
  self.sharedLibTarget.build

-- # Build Package Bin

protected def Package.binTarget (self : Package) : FileTarget :=
  Target.mk self.binFile do
    let depTargets ← self.buildDepTargets buildOleanAndCTargetWithDepTargets
    let depTarget ← self.buildDepTargetWith depTargets
    let build := self.recBuildModuleOleanAndCTargetWithLocalImports depTarget
    let pkgTarget ← self.buildModuleDAGTarget self.binRoot build
    let linkTargets :=
      pkgTarget.oFileTargets ++ self.moreLibTargets ++
      depTargets.concatMap (·.staticLibTargets)
    let target := leanBinTarget self.binFile linkTargets self.moreLinkArgs
    target.materializeAsync

def Package.buildBin (self : Package) : BuildM FilePath :=
  self.binTarget.build
