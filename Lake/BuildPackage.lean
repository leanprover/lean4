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

abbrev ActivePackageTarget := ActiveBuildTarget (Package × ModuleTargetMap)

namespace ActivePackageTarget

def package (self : ActivePackageTarget) :=
  self.info.1

def moduleTargetMap (self : ActivePackageTarget) : ModuleTargetMap :=
  self.info.2

def moduleTargets (self : ActivePackageTarget) : Array (Name × ActiveModuleTarget) :=
  self.moduleTargetMap.fold (fun arr k v => arr.push (k, v)) #[]

end ActivePackageTarget

-- # Build Modules

def Package.buildModuleTargetDAGFor
(mod : Name) (moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget)
(self : Package) : BuildM (ActiveModuleTarget × ModuleTargetMap) := do
  let fetch := recFetchModuleTargetWithLocalImports self moreOleanDirs depTarget
  failOnImportCycle <| ← buildRBTop fetch mod |>.run {}

def Package.buildOleanTargetDAGFor
(mod : Name) (moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget)
(self : Package) : BuildM (OleanTarget × OleanTargetMap) := do
  let fetch := recFetchModuleOleanTargetWithLocalImports self moreOleanDirs depTarget
  failOnImportCycle <| ← buildRBTop fetch mod |>.run {}

def Package.buildModuleTargetDAG
(moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget) (self : Package) :=
  self.buildModuleTargetDAGFor self.moduleRoot moreOleanDirs depTarget

def Package.buildOleanTargetDAG
(moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget) (self : Package) :=
  self.buildOleanTargetDAGFor self.moduleRoot moreOleanDirs depTarget

def Package.buildModuleTargets
(mods : List Name) (moreOleanDirs : List FilePath)
(depTarget : ActiveOpaqueTarget) (self : Package)
: BuildM (List ActiveModuleTarget) := do
  let fetch : ModuleTargetFetch :=
    recFetchModuleTargetWithLocalImports self moreOleanDirs depTarget
  failOnImportCycle <| ← mods.mapM (buildRBTop fetch) |>.run' {}

def Package.buildOleanTargets
(mods : List Name) (moreOleanDirs : List FilePath)
(depTarget : ActiveOpaqueTarget) (self : Package)
: BuildM (List OleanTarget) := do
  let fetch : OleanTargetFetch :=
    recFetchModuleOleanTargetWithLocalImports self moreOleanDirs depTarget
  failOnImportCycle <| ← mods.mapM (buildRBTop fetch) |>.run' {}

def Package.buildRootModuleTarget
(moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget) (self : Package) :=
  self.buildModuleTargets [self.moduleRoot] moreOleanDirs depTarget |>.map (·.get! 0)

def Package.buildRootOleanTarget
(moreOleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget) (self : Package) :=
  self.buildOleanTargets [self.moduleRoot] moreOleanDirs depTarget |>.map (·.get! 0)

-- # Configure/Build Packages

def Package.buildDepTargetWith
(depTargets : List ActivePackageTarget) (self : Package) : BuildM ActiveOpaqueTarget := do
  let extraDepTarget ← self.extraDepTarget.run
  let depTarget ← ActiveTarget.collectOpaqueList depTargets
  extraDepTarget.mixOpaqueAsync depTarget

def Package.buildTargetWithDepTargetsFor
(mod : Name) (depTargets : List ActivePackageTarget) (self : Package)
: BuildM ActivePackageTarget := do
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := depTargets.map (·.package.oleanDir)
  let (target, targetMap) ← self.buildModuleTargetDAGFor mod moreOleanDirs depTarget
  return target.withInfo ⟨self, targetMap⟩

def Package.buildTargetWithDepTargets
(depTargets : List ActivePackageTarget) (self : Package) : BuildM ActivePackageTarget :=
  self.buildTargetWithDepTargetsFor self.moduleRoot depTargets

partial def Package.buildTarget (self : Package) : BuildM ActivePackageTarget := do
  let deps ← solveDeps self
  -- build dependencies recursively
  -- TODO: share build of common dependencies
  let depTargets ← deps.mapM (·.buildTarget)
  self.buildTargetWithDepTargets depTargets

def Package.buildDepTargets (self : Package) : BuildM (List ActivePackageTarget) := do
  let deps ← solveDeps self
  deps.mapM (·.buildTarget)

def Package.buildDeps (self : Package) : BuildM (List Package) := do
  let deps ← solveDeps self
  let targets ← deps.mapM (·.buildTarget)
  targets.forM (discard ·.materialize)
  return deps

def configure (pkg : Package) : IO Unit :=
  runBuild pkg.buildDeps

def Package.build (self : Package) : BuildM PUnit := do
  let depTargets ← self.buildDepTargets
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := depTargets.map (·.package.oleanDir)
  let target ← self.buildRootOleanTarget moreOleanDirs depTarget
  discard target.materialize

def build (pkg : Package) : IO PUnit :=
  runBuild pkg.build

-- # Print Paths

def Package.buildOleanTargetsWithDeps
(deps : List Package) (mods : List Name) (self : Package)
: BuildM (List OleanTarget) := do
  let moreOleanDirs := deps.map (·.oleanDir)
  let depTarget ← self.buildDepTargetWith <| ← deps.mapM (·.buildTarget)
  self.buildOleanTargets mods moreOleanDirs depTarget

def Package.buildOleansWithDeps
(deps : List Package) (mods : List Name)  (self : Package) :=
  self.buildOleanTargetsWithDeps deps mods >>= (·.forM (discard ·.materialize))

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← solveDeps pkg
  unless imports.isEmpty do
    let imports := imports.map (·.toName)
    let localImports := imports.filter (·.getRoot == pkg.moduleRoot)
    runBuild <| pkg.buildOleansWithDeps deps localImports
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.srcDir :: deps.map (·.srcDir)
