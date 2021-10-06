/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.BuildPackage
import Lake.BuildTargets

open System
namespace Lake

-- # Build Package .o Files

def ActivePackageTarget.oFileTargets
(self : ActivePackageTarget) : Array FileTarget :=
  let leancArgs := self.package.leancArgs
  self.moduleTargets.map fun (mod, target) =>
    let oFile := self.package.modToO mod
    let cTarget := Target.active target.cTarget
    leanOFileTarget oFile cTarget leancArgs

-- # Build Package Lib

protected def ActivePackageTarget.staticLibTarget (self : ActivePackageTarget) : FileTarget :=
  staticLibTarget self.package.staticLibFile self.oFileTargets

def ActivePackageTarget.staticLibTargets (self : ActivePackageTarget) : Array FileTarget :=
  #[self.staticLibTarget] ++ self.package.moreLibTargets

def Package.staticLibTarget (self : Package) : FileTarget :=
 Target.mk self.staticLibFile do
    (← self.buildTarget).staticLibTarget.materializeAsync

def Package.buildLib (pkg : Package) : BuildM FilePath :=
  pkg.staticLibTarget.build

-- # Build Package Bin

def ActivePackageTarget.linkTargets
(depTargets : Array ActivePackageTarget) (self : ActivePackageTarget) : Array FileTarget :=
  self.oFileTargets ++ self.package.moreLibTargets ++ depTargets.concatMap (·.staticLibTargets)

protected def ActivePackageTarget.binTarget
(depTargets : Array ActivePackageTarget) (self : ActivePackageTarget) : FileTarget :=
  let linkTargets := self.linkTargets depTargets
  leanBinTarget self.package.binFile linkTargets self.package.linkArgs

def Package.binTarget (self : Package) : FileTarget :=
  Target.mk self.binFile do
    let depTargets ← self.buildDepTargets
    let pkgTarget ← self.buildModuleOleanAndCTargetsWithDepTargets #[self.binRoot] depTargets
    pkgTarget.binTarget depTargets >>= (·.materializeAsync)

def Package.buildBin (pkg : Package) : BuildM FilePath :=
  pkg.binTarget.build
