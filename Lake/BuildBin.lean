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
def skipIfNewer [GetMTime i]
(info : i) (depTarget : ActiveBuildTarget α)
(build : α → BuildM PUnit) : BuildM (ActiveBuildTarget i) := do
  ActiveTarget.mk info <| ← depTarget.mapAsync fun depInfo depTrace => do
    unless (← checkIfNewer info depTrace.mtime) do
      build depInfo
    depTrace

-- # Build `.o` Files

-- def buildLeanO (oFile : FilePath)
-- (cTarget : ActiveFileTarget) (leancArgs : Array String := #[])
-- : BuildM (BuildTask PUnit) :=
--   cTarget >> compileLeanO oFile cTarget.artifact leancArgs

def fetchLeanOFileTarget (oFile : FilePath)
(cTarget : ActiveFileTarget) (leancArgs : Array String := #[])
: BuildM ActiveFileTarget := do
  skipIfNewer oFile cTarget fun cFile => compileLeanO oFile cFile leancArgs

-- # Build Package Lib

def PackageTarget.fetchOFileTargets
(self : PackageTarget) : BuildM (Array ActiveFileTarget) := do
  self.moduleTargets.mapM fun (mod, target) =>
    fetchLeanOFileTarget (self.package.modToO mod) target.cTarget self.package.leancArgs

def PackageTarget.fetchStaticLibTarget (self : PackageTarget) : BuildM ActiveFileTarget :=  do
  let oFilesTarget ← ActiveTarget.collectArray (← self.fetchOFileTargets)
  skipIfNewer self.package.staticLibFile oFilesTarget fun oFiles =>
    compileStaticLib self.package.staticLibFile oFiles

def PackageTarget.fetchStaticLibTargets (self : PackageTarget) : BuildM (Array ActiveFileTarget) := do
  #[← self.fetchStaticLibTarget] ++ (← self.package.moreLibTargets.mapM (·.run))

def Package.fetchStaticLibTarget (self : Package) : BuildM ActiveFileTarget := do
  (← self.buildTarget).fetchStaticLibTarget

def Package.fetchStaticLib (self : Package) : BuildM FilePath := do
  let target ← self.fetchStaticLibTarget
  discard target.materialize
  return target.info

def buildLib (pkg : Package) : IO PUnit :=
  runBuild pkg.fetchStaticLib

-- # Build Package Bin

def PackageTarget.fetchBinTarget
(depTargets : List PackageTarget) (self : PackageTarget) : BuildM ActiveFileTarget := do
  let oFileTargets ← self.fetchOFileTargets
  let depLibTargets ← depTargets.foldlM
    (fun ts dep => do pure <| ts ++ (← dep.fetchStaticLibTargets)) #[]
  let moreLibTargets ← self.package.moreLibTargets.mapM (·.run)
  let linkTargets := oFileTargets ++ depLibTargets ++ moreLibTargets
  let linksTarget ← ActiveTarget.collectArray linkTargets
  skipIfNewer self.package.binFile linksTarget fun links =>
     compileLeanBin self.package.binFile links self.package.linkArgs

def Package.fetchBinTarget (self : Package) : BuildM ActiveFileTarget := do
  let depTargets ← self.buildDepTargets
  let pkgTarget ← self.buildTargetWithDepTargets depTargets
  pkgTarget.fetchBinTarget depTargets

def Package.fetchBin (self : Package) : BuildM FilePath := do
  let target ← self.fetchBinTarget
  discard target.materialize
  return target.info

def buildBin (pkg : Package) : IO PUnit :=
  runBuild pkg.fetchBin
