/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build

open System
namespace Lake

-- # Build `.o` Files

def buildLeanO (oFile : FilePath)
(cTarget : ActiveBuildTarget t FilePath) (leancArgs : Array String := #[]) : IO (IOTask PUnit) :=
  cTarget >> compileLeanO oFile cTarget.artifact leancArgs

def fetchLeanOFileTarget (oFile : FilePath)
(cTarget : ActiveFileTarget) (leancArgs : Array String := #[]) : IO ActiveFileTarget :=
  skipIfNewer oFile cTarget.mtime <| buildLeanO oFile cTarget leancArgs

-- # Build Package Lib

def PackageTarget.fetchOFileTargets
(self : PackageTarget) : IO (Array ActiveFileTarget) := do
  self.moduleTargets.mapM fun (mod, target) => do
    let oFile := self.package.modToO mod
    fetchLeanOFileTarget (oFile) target.cTarget self.package.leancArgs

def PackageTarget.buildStaticLib
(self : PackageTarget) : IO (IOTask PUnit) := do
  let oFileTargets ← self.fetchOFileTargets
  let oFiles := oFileTargets.map (·.artifact)
  oFileTargets >> compileStaticLib self.package.staticLibFile oFiles

def PackageTarget.fetchStaticLibTarget (self : PackageTarget) : IO ActiveFileTarget := do
  skipIfNewer self.package.staticLibFile self.mtime self.buildStaticLib

def Package.fetchStaticLibTarget (self : Package) : IO ActiveFileTarget := do
  (← self.buildTarget).fetchStaticLibTarget

def Package.fetchStaticLib (self : Package) : IO FilePath := do
  let target ← self.fetchStaticLibTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildLib (pkg : Package) : IO PUnit :=
  discard pkg.fetchStaticLib

-- # Build Package Bin

def PackageTarget.buildBin
(depTargets : List PackageTarget) (self : PackageTarget)
: IO (IOTask PUnit) := do
  let oFileTargets ← self.fetchOFileTargets
  let libTargets ← depTargets.mapM (·.fetchStaticLibTarget)
  let moreLibTargets ← self.package.buildMoreLibTargets
  let linkTargets := oFileTargets ++ libTargets ++ moreLibTargets
  let linkFiles := linkTargets.map (·.artifact)
  linkTargets >> compileLeanBin self.package.binFile linkFiles self.package.linkArgs

def PackageTarget.fetchBinTarget
(depTargets : List PackageTarget) (self : PackageTarget) : IO ActiveFileTarget :=
  skipIfNewer self.package.binFile self.mtime <| self.buildBin depTargets

def Package.fetchBinTarget (self : Package) : IO ActiveFileTarget := do
  let depTargets ← self.buildDepTargets
  let pkgTarget ← self.buildTargetWithDepTargets depTargets
  pkgTarget.fetchBinTarget depTargets

def Package.fetchBin (self : Package) : IO FilePath := do
  let target ← self.fetchBinTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within the task
    throw <| IO.userError "Build failed."
  return target.artifact

def buildBin (pkg : Package) : IO PUnit :=
  discard pkg.fetchBin
