/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sebastian Ullrich, Mac Malone
-/
import Lean.Data.Name
import Lean.Elab.Import
import Lake.Target
import Lake.BuildModule
import Lake.Resolve
import Lake.Package

open System
open Lean hiding SearchPath

namespace Lake

-- # Build Target

abbrev ActivePackageTarget := ActiveBuildTarget (Package × NameMap ActiveOleanAndCTarget)

namespace ActivePackageTarget

def package (self : ActivePackageTarget) :=
  self.info.1

def moduleTargetMap (self : ActivePackageTarget) : NameMap ActiveOleanAndCTarget :=
  self.info.2

def moduleTargets (self : ActivePackageTarget) : Array (Name × ActiveOleanAndCTarget) :=
  self.moduleTargetMap.fold (fun arr k v => arr.push (k, v)) #[]

end ActivePackageTarget

-- # Build Modules

def Package.buildModuleOleanAndCTargetDAG
(mods : Array Name) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveOleanAndCTarget × OleanAndCTargetMap) := do
  let fetch : OleanAndCTargetFetch :=
    self.recFetchModuleOleanAndCTargetWithLocalImports moreOleanDirs depTarget
  failOnImportCycle <| ← mods.mapM (buildRBTop fetch) |>.run {}

def Package.buildModuleOleanTargetDAG
(mods : Array Name) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveFileTarget × OleanTargetMap) := do
  let fetch : OleanTargetFetch :=
    self.recFetchModuleOleanTargetWithLocalImports moreOleanDirs depTarget
  failOnImportCycle <| ← mods.mapM (buildRBTop fetch) |>.run {}

def Package.buildOleanAndCTargetDAG
(moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveOleanAndCTarget × OleanAndCTargetMap) := do
  self.buildModuleOleanAndCTargetDAG (← self.getModuleArray) moreOleanDirs depTarget

def Package.buildOleanTargetDAG
(moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveFileTarget × OleanTargetMap) := do
  self.buildModuleOleanTargetDAG (← self.getModuleArray) moreOleanDirs depTarget

def Package.buildModuleOleanAndCTargets
(mods : Array Name) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveOleanAndCTarget) := do
  let fetch : OleanAndCTargetFetch :=
    self.recFetchModuleOleanAndCTargetWithLocalImports moreOleanDirs depTarget
  failOnImportCycle <| ← mods.mapM (buildRBTop fetch) |>.run' {}

def Package.buildModuleOleanTargets
(mods : Array Name) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveFileTarget) := do
  let fetch : OleanTargetFetch :=
    self.recFetchModuleOleanTargetWithLocalImports moreOleanDirs depTarget
  failOnImportCycle <| ← mods.mapM (buildRBTop fetch) |>.run' {}

def Package.buildOleanAndCTargets
(moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveOleanAndCTarget) := do
  self.buildModuleOleanAndCTargets (← self.getModuleArray) moreOleanDirs depTarget

def Package.buildOleanTargets
(moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveFileTarget) := do
  self.buildModuleOleanTargets (← self.getModuleArray) moreOleanDirs depTarget

-- # Configure/Build Packages

def Package.buildDepTargetWith
(depTargets : List ActivePackageTarget) (self : Package) : BuildM ActiveOpaqueTarget := do
  let extraDepTarget ← self.extraDepTarget.run
  let depTarget ← ActiveTarget.collectOpaqueList depTargets
  extraDepTarget.mixOpaqueAsync depTarget

def Package.buildModuleOleanAndCTargetsWithDepTargets
(mods : Array Name) (depTargets : List ActivePackageTarget) (self : Package)
: BuildM ActivePackageTarget := do
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := depTargets.map (·.package.oleanDir)
  let (targets, targetMap) ← self.buildModuleOleanAndCTargetDAG mods moreOleanDirs depTarget
  let target ← ActiveTarget.collectOpaqueArray targets
  return target.withInfo ⟨self, targetMap⟩

def Package.buildOleanAndCTargetsWithDepTargets
(depTargets : List ActivePackageTarget) (self : Package) : BuildM ActivePackageTarget := do
  self.buildModuleOleanAndCTargetsWithDepTargets (← self.getModuleArray) depTargets

/--
  The main package build function.

  It resolves the package's dependencies and recursively builds them.
  For each package, it compiles its modules into `.olean` and `.c` files.
-/
partial def Package.buildTarget (self : Package) : BuildM ActivePackageTarget := do
  let deps ← solveDeps self
  -- build dependencies recursively
  -- TODO: share build of common dependencies
  let depTargets ← deps.mapM (·.buildTarget)
  self.buildOleanAndCTargetsWithDepTargets depTargets

def Package.buildDepTargets (self : Package) : BuildM (List ActivePackageTarget) := do
  let deps ← solveDeps self
  deps.mapM (·.buildTarget)

def Package.buildDeps (self : Package) : BuildM (List Package) := do
  let deps ← solveDeps self
  let targets ← deps.mapM (·.buildTarget)
  targets.forM (discard ·.materialize)
  return deps

def configure (pkg : Package) : IO Unit :=
  pkg.buildDeps.run

def Package.build (self : Package) : BuildM PUnit := do
  let depTargets ← self.buildDepTargets
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := depTargets.map (·.package.oleanDir)
  let targets ← self.buildOleanTargets moreOleanDirs depTarget
  discard <| ActiveTarget.materializeArray targets

def build (pkg : Package) : IO PUnit :=
  pkg.build.run

-- # Print Paths

def Package.buildModuleOleanTargetsWithDeps
(deps : List Package) (mods : Array Name) (self : Package)
: BuildM (Array ActiveFileTarget) := do
  let moreOleanDirs := deps.map (·.oleanDir)
  let depTarget ← self.buildDepTargetWith <| ← deps.mapM (·.buildTarget)
  self.buildModuleOleanTargets mods moreOleanDirs depTarget

def Package.buildModuleOleansWithDeps
(deps : List Package) (mods : Array Name) (self : Package) :=
  self.buildModuleOleanTargetsWithDeps deps mods >>= (·.forM (discard ·.materialize))

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← solveDeps pkg
  unless imports.isEmpty do
    let imports := imports.map (·.toName)
    let localImports := imports.filter pkg.isLocalModule |>.toArray
    pkg.buildModuleOleansWithDeps deps localImports |>.run
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.srcDir :: deps.map (·.srcDir)
