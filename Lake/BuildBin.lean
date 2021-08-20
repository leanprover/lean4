/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.BuildPackage

open System
namespace Lake

/--
  Construct a no-op target if the given artifact is up-to-date.
  Otherwise, construct a target with the given build task.
-/
def skipIfNewer
[GetMTime a] (artifact : a) (trace : LakeTrace)
(build : BuildM (BuildTask PUnit)) : BuildM (ActiveBuildTarget a) := do
  ActiveTarget.mk artifact trace <| ←
    skipIf (← checkIfNewer artifact trace.mtime) build

-- # Build `.o` Files

def buildLeanO (oFile : FilePath)
(cTarget : ActiveFileTarget) (leancArgs : Array String := #[])
: BuildM (BuildTask PUnit) :=
  cTarget >> compileLeanO oFile cTarget.artifact leancArgs

def fetchLeanOFileTarget (oFile : FilePath)
(cTarget : ActiveFileTarget) (leancArgs : Array String := #[])
: BuildM ActiveFileTarget :=
  skipIfNewer oFile cTarget.trace <| buildLeanO oFile cTarget leancArgs

-- # Build Package Lib

def PackageTarget.fetchOFileTargets
(self : PackageTarget) : BuildM (Array ActiveFileTarget) := do
  self.moduleTargets.mapM fun (mod, target) => do
    let oFile := self.package.modToO mod
    fetchLeanOFileTarget (oFile) target.cTarget self.package.leancArgs

def PackageTarget.buildStaticLib
(self : PackageTarget) : BuildM (IOTask PUnit) := do
  let oFileTargets ← self.fetchOFileTargets
  let oFiles := oFileTargets.map (·.artifact)
  oFileTargets >> compileStaticLib self.package.staticLibFile oFiles

def PackageTarget.fetchStaticLibTarget (self : PackageTarget) : BuildM ActiveFileTarget := do
  skipIfNewer self.package.staticLibFile self.trace self.buildStaticLib

def PackageTarget.fetchStaticLibTargets (self : PackageTarget) : BuildM (Array ActiveFileTarget) := do
  #[← self.fetchStaticLibTarget] ++ (← self.package.buildMoreLibTargets)

def Package.fetchStaticLibTarget (self : Package) : BuildM ActiveFileTarget := do
  (← self.buildTarget).fetchStaticLibTarget

def Package.fetchStaticLib (self : Package) : BuildM FilePath := do
  let target ← self.fetchStaticLibTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within target
    BuildM.logError "Build failed."
  return target.artifact

def buildLib (pkg : Package) : IO PUnit :=
  runBuild pkg.fetchStaticLib

-- # Build Package Bin

def PackageTarget.buildBin
(depTargets : List PackageTarget) (self : PackageTarget)
: BuildM (IOTask PUnit) := do
  let oFileTargets ← self.fetchOFileTargets
  let depLibTargets ← depTargets.foldlM
    (fun ts dep => do pure <| ts ++ (← dep.fetchStaticLibTargets)) #[]
  let moreLibTargets ← self.package.buildMoreLibTargets
  let linkTargets := oFileTargets ++ depLibTargets ++ moreLibTargets
  let linkFiles := linkTargets.map (·.artifact)
  linkTargets >> compileLeanBin self.package.binFile linkFiles self.package.linkArgs

def PackageTarget.fetchBinTarget
(depTargets : List PackageTarget) (self : PackageTarget) : BuildM ActiveFileTarget :=
  skipIfNewer self.package.binFile self.trace <| self.buildBin depTargets

def Package.fetchBinTarget (self : Package) : BuildM ActiveFileTarget := do
  let depTargets ← self.buildDepTargets
  let pkgTarget ← self.buildTargetWithDepTargets depTargets
  pkgTarget.fetchBinTarget depTargets

def Package.fetchBin (self : Package) : BuildM FilePath := do
  let target ← self.fetchBinTarget
  try target.materialize catch _ =>
    -- actual error has already been printed within target
    BuildM.logError "Build failed."
  return target.artifact

def buildBin (pkg : Package) : IO PUnit :=
  runBuild pkg.fetchBin
