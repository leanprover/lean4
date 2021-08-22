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

abbrev PackageTarget := ActiveBuildTarget (Package × NameMap ModuleTarget)

namespace PackageTarget

def package (self : PackageTarget) :=
  self.artifact.1

def moduleTargetMap (self : PackageTarget) : NameMap ModuleTarget :=
  self.artifact.2

def moduleTargets (self : PackageTarget) : Array (Name × ModuleTarget) :=
  self.moduleTargetMap.fold (fun arr k v => arr.push (k, v)) #[]

end PackageTarget

-- # Build Modules

def Package.buildModuleTargetDAGFor
(mod : Name)  (oleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget)
(self : Package) : BuildM (ModuleTarget × NameMap ModuleTarget) := do
  let fetch := fetchModuleWithLocalImports self oleanDirs depTarget
  failOnCycle <| ← buildRBTop fetch mod |>.run {}

def Package.buildModuleTargetDAG
(oleanDirs : List FilePath) (depTarget : ActiveOpaqueTarget) (self : Package) :=
  self.buildModuleTargetDAGFor self.moduleRoot oleanDirs depTarget

def Package.buildModuleTargets
(mods : List Name) (oleanDirs : List FilePath)
(depTarget : ActiveOpaqueTarget) (self : Package)
: BuildM (List ModuleTarget) := do
  let fetch : ModuleTargetFetch := fetchModuleWithLocalImports self oleanDirs depTarget
  failOnCycle <| ← mods.mapM (buildRBTop fetch) |>.run' {}

-- # Configure/Build Packages

def Package.buildTargetWithDepTargetsFor
(mod : Name) (depTargets : List PackageTarget) (self : Package)
: BuildM PackageTarget := do
  let extraDepTarget ← self.buildExtraDepTarget
  let depTarget ← ActiveOpaqueTarget.collectList depTargets
  let allDepsTarget ← extraDepTarget.andThenTargetAsync depTarget
  let oleanDirs := depTargets.map (·.package.oleanDir)
  let (target, targetMap) ← self.buildModuleTargetDAGFor mod oleanDirs allDepsTarget
  return {target with artifact := ⟨self, targetMap⟩}

def Package.buildTargetWithDepTargets
(depTargets : List PackageTarget) (self : Package) : BuildM PackageTarget :=
  self.buildTargetWithDepTargetsFor self.moduleRoot depTargets

partial def Package.buildTarget (self : Package) : BuildM PackageTarget := do
  let deps ← solveDeps self
  -- build dependencies recursively
  -- TODO: share build of common dependencies
  let depTargets ← deps.mapM (·.buildTarget)
  self.buildTargetWithDepTargets depTargets

def Package.buildDepTargets (self : Package) : BuildM (List PackageTarget) := do
  let deps ← solveDeps self
  deps.mapM (·.buildTarget)

def Package.buildDeps (self : Package) : BuildM (List Package) := do
  let deps ← solveDeps self
  let targets ← deps.mapM (·.buildTarget)
  targets.forM (·.materialize)
  return deps

def configure (pkg : Package) : IO Unit :=
  runBuild pkg.buildDeps

def Package.build (self : Package) : BuildM PUnit := do
  (← self.buildTarget).materialize

def build (pkg : Package) : IO PUnit :=
  runBuild pkg.build

-- # Print Paths

def Package.buildModuleTargetsWithDeps
(deps : List Package) (mods : List Name)  (self : Package)
: BuildM (List ModuleTarget) := do
  let oleanDirs := deps.map (·.oleanDir)
  let extraDepTarget ← self.buildExtraDepTarget
  let depTarget ← ActiveOpaqueTarget.collectList <| ← deps.mapM (·.buildTarget)
  let allDepsTarget ← extraDepTarget.andThenTargetAsync depTarget
  self.buildModuleTargets mods oleanDirs allDepsTarget

def Package.buildModulesWithDeps
(deps : List Package) (mods : List Name)  (self : Package)
: BuildM PUnit := do
  (← self.buildModuleTargetsWithDeps deps mods).forM (·.materialize)

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← solveDeps pkg
  unless imports.isEmpty do
    let imports := imports.map (·.toName)
    let localImports := imports.filter (·.getRoot == pkg.moduleRoot)
    runBuild <| pkg.buildModulesWithDeps deps localImports
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.srcDir :: deps.map (·.srcDir)
