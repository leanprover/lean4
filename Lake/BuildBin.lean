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
    oFileTarget oFile cTarget leancArgs "leanc"

-- # Build Package Lib

protected def ActivePackageTarget.staticLibTarget (self : ActivePackageTarget) : FileTarget :=
  staticLibTarget self.package.staticLibFile self.oFileTargets

def ActivePackageTarget.staticLibTargets (self : ActivePackageTarget) : Array FileTarget :=
  #[self.staticLibTarget] ++ self.package.moreLibTargets

def Package.staticLibTarget (self : Package) : FileTarget :=
 Target.mk self.staticLibFile do
    (← self.buildTarget).staticLibTarget.materializeAsync

def buildLib (pkg : Package) : IO PUnit :=
  pkg.staticLibTarget.build.run

-- # Build Package Bin

def ActivePackageTarget.linkTargets
(depTargets : List ActivePackageTarget) (self : ActivePackageTarget) : Array FileTarget :=
  depTargets.foldl (fun ts dep => ts ++ dep.staticLibTargets) <|
    self.oFileTargets ++ self.package.moreLibTargets

protected def ActivePackageTarget.binTarget
(depTargets : List ActivePackageTarget) (self : ActivePackageTarget) : FileTarget :=
  let linkTargets := self.linkTargets depTargets
  binTarget self.package.binFile linkTargets self.package.linkArgs "leanc"

def Package.binTarget (self : Package) : FileTarget :=
  Target.mk self.binFile do
    let depTargets ← self.buildDepTargets
    let pkgTarget ← self.buildModuleOleanAndCTargetsWithDepTargets self.binRoot depTargets
    pkgTarget.binTarget depTargets >>= (·.materializeAsync)

def buildBin (pkg : Package) : IO PUnit :=
  pkg.binTarget.build.run
