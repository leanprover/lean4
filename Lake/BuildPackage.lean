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

/-- Returns the `oleanDir`s of the given package targets in reverse order. -/
def packageTargetsToOleanDirs (targets : Array ActivePackageTarget) : List FilePath :=
  targets.map (·.package.oleanDir) |>.foldl (flip List.cons) []

-- # Build Modules

def Package.buildModuleOleanAndCTargetDAG
(mods : Array Name) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveOleanAndCTarget × OleanAndCTargetMap) := do
  let buildMod : OleanAndCTargetBuild :=
    self.recBuildModuleOleanAndCTargetWithLocalImports moreOleanDirs depTarget
  let (resE, map) ← mods.mapM (buildRBTop buildMod id) |>.run
  (← failOnBuildCycle resE, map)

def Package.buildModuleOleanTargetDAG
(mods : Array Name) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveFileTarget × OleanTargetMap) := do
  let buildMod : OleanTargetBuild :=
    self.recBuildModuleOleanTargetWithLocalImports moreOleanDirs depTarget
  let (resE, map) ← RBTopT.run <| mods.mapM (buildRBTop buildMod id)
  (← failOnBuildCycle resE, map)

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
  let buildMod : OleanAndCTargetBuild :=
    self.recBuildModuleOleanAndCTargetWithLocalImports moreOleanDirs depTarget
  failOnBuildCycle <| ← RBTopT.run' <| mods.mapM <| buildRBTop buildMod id

def Package.buildModuleOleanTargets
(mods : Array Name) (moreOleanDirs : List FilePath) (depTarget : ActiveBuildTarget x)
(self : Package) : BuildM (Array ActiveFileTarget) := do
  let buildMod : OleanTargetBuild :=
    self.recBuildModuleOleanTargetWithLocalImports moreOleanDirs depTarget
  failOnBuildCycle <| ← RBTopT.run' <| mods.mapM <| buildRBTop buildMod id

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
(depTargets : Array ActivePackageTarget) (self : Package) : BuildM ActiveOpaqueTarget := do
  let extraDepTarget ← self.extraDepTarget.run
  let depTarget ← ActiveTarget.collectOpaqueArray depTargets
  extraDepTarget.mixOpaqueAsync depTarget

def Package.buildModuleOleanAndCTargetsWithDepTargets
(mods : Array Name) (depTargets : Array ActivePackageTarget) (self : Package)
: BuildM ActivePackageTarget := do
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := packageTargetsToOleanDirs depTargets
  let (targets, targetMap) ← self.buildModuleOleanAndCTargetDAG mods moreOleanDirs depTarget
  let target ← ActiveTarget.collectOpaqueArray targets
  return target.withInfo ⟨self, targetMap⟩

def Package.buildOleanAndCTargetsWithDepTargets
(depTargets : Array ActivePackageTarget) (self : Package) : BuildM ActivePackageTarget := do
  self.buildModuleOleanAndCTargetsWithDepTargets (← self.getModuleArray) depTargets

/--
  The main package build function.

  It resolves the package's dependencies and recursively builds them.
  For each package, it compiles its modules into `.olean` and `.c` files.
-/
def recBuildPackageWithDeps
[Monad m] [MonadLiftT BuildM m] [MonadStore Name (Array ActivePackageTarget) m]
: RecBuild Package (Array ActivePackageTarget) m := fun pkg buildPkg => do
  let mut depTargets := #[]
  for dep in pkg.dependencies do
    let targets? ← fetch? dep.name.toName
    let targets ← do
      if let some targets := targets? then
        pure targets
      else
        let depPkg ← liftM (m := BuildM) <| resolveDep pkg dep
        buildPkg depPkg
    depTargets := depTargets ++ targets
  let pkgTarget ← pkg.buildOleanAndCTargetsWithDepTargets depTargets
  depTargets.push pkgTarget

def buildPackageTargetsWithDeps (pkgs : Array Package) : BuildM (Array ActivePackageTarget) := do
  failOnBuildCycle <| ← RBTopT.run' <| pkgs.concatMapM fun pkg =>
    buildRBTop (cmp := Name.quickCmp) recBuildPackageWithDeps (·.name.toName) pkg

def Package.buildTarget (self : Package) : BuildM ActivePackageTarget := do
  (← buildPackageTargetsWithDeps #[self]).back

def Package.buildDepTargets (self : Package) : BuildM (Array ActivePackageTarget) := do
  buildPackageTargetsWithDeps (← self.resolveDirectDeps).toArray

def Package.buildDeps (self : Package) : BuildM (Array Package) := do
  let targets ← self.buildDepTargets
  targets.mapM fun target => Functor.mapConst target.info.1 target.materialize

def configure (pkg : Package) : IO Unit :=
  pkg.buildDeps.run

def Package.build (self : Package) : BuildM PUnit := do
  let depTargets ← self.buildDepTargets
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := packageTargetsToOleanDirs depTargets
  let targets ← self.buildOleanTargets moreOleanDirs depTarget
  discard <| ActiveTarget.materializeArray targets

def build (pkg : Package) : IO PUnit :=
  pkg.build.run

-- # Print Paths

/-- Pick the local imports of the package from a list of import strings. -/
def Package.filterLocalImports (imports : List String) (self : Package) : Array Name := do
  let mut localImports := #[]
  for imp in imports do
    let impName := imp.toName
    if self.isLocalModule impName then
      localImports := localImports.push impName
  return localImports

def printPaths (pkg : Package) (imports : List String := []) : IO Unit := do
  let deps ← BuildM.run' do
    -- resolve and build deps
    let depTargets ← pkg.buildDepTargets
    let depPkgs := depTargets.map (·.package) |>.foldl (flip List.cons) []
    -- build any additional imports
    unless imports.isEmpty do
      let moreOleanDirs := depPkgs.map (·.oleanDir)
      let depTarget ← pkg.buildDepTargetWith depTargets
      let localImports := pkg.filterLocalImports imports
      let oleanTargets ← pkg.buildModuleOleanTargets localImports moreOleanDirs depTarget
      oleanTargets.forM (discard ·.materialize)
    pure depPkgs
  IO.println <| SearchPath.toString <| pkg.oleanDir :: deps.map (·.oleanDir)
  IO.println <| SearchPath.toString <| pkg.srcDir :: deps.map (·.srcDir)
