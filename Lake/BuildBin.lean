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

def PackageTarget.oFileTargets
(self : PackageTarget) : Array FileTarget :=
  let leancArgs := self.package.leancArgs
  self.moduleTargets.map fun (mod, target) =>
    let oFile := self.package.modToO mod
    let cTarget := Target.active target.cTarget
    oFileTarget oFile cTarget leancArgs "leanc"

-- # Build Package Lib

protected def PackageTarget.staticLibTarget (self : PackageTarget) : FileTarget :=
  staticLibTarget self.package.staticLibFile self.oFileTargets

def PackageTarget.staticLibTargets (self : PackageTarget) : Array FileTarget :=
  #[self.staticLibTarget] ++ self.package.moreLibTargets

def Package.staticLibTarget (self : Package) : FileTarget :=
 Target.mk self.staticLibFile do
    (← self.buildTarget).staticLibTarget.materializeAsync

def buildLib (pkg : Package) : IO PUnit :=
  runBuild pkg.staticLibTarget.build

-- # Build Package Bin

def PackageTarget.linkTargets
(depTargets : List PackageTarget) (self : PackageTarget) : Array FileTarget :=
  depTargets.foldl (fun ts dep => ts ++ dep.staticLibTargets) <|
    self.oFileTargets ++ self.package.moreLibTargets

protected def PackageTarget.binTarget
(depTargets : List PackageTarget) (self : PackageTarget) : FileTarget :=
  let linkTargets := self.linkTargets depTargets
  binTarget self.package.binFile linkTargets self.package.linkArgs "leanc"

def Package.binTarget (self : Package) : FileTarget :=
  Target.mk self.binFile do
    let depTargets ← self.buildDepTargets
    let pkgTarget ← self.buildTargetWithDepTargets depTargets
    pkgTarget.binTarget depTargets >>= (·.materializeAsync)

def buildBin (pkg : Package) : IO PUnit :=
  runBuild pkg.binTarget.build
