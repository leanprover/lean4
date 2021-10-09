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

abbrev PackageTarget := BuildTarget Package

abbrev ActivePackageTarget i := ActiveBuildTarget (Package × NameMap (ActiveBuildTarget i))

namespace ActivePackageTarget

def package (self : ActivePackageTarget i) :=
  self.info.1

def moduleTargetMap (self : ActivePackageTarget i) : NameMap (ActiveBuildTarget i) :=
  self.info.2

def moduleTargets (self : ActivePackageTarget i) : Array (Name × ActiveBuildTarget i) :=
  self.moduleTargetMap.fold (fun arr k v => arr.push (k, v)) #[]

end ActivePackageTarget

/-- Returns the `oleanDir`s of the given package targets in reverse order. -/
def packageTargetsToOleanDirs (targets : Array (ActivePackageTarget i)) : List FilePath :=
  targets.map (·.package.oleanDir) |>.foldl (flip List.cons) []

-- # Build Packages

/--
  Builds the package's `extraDepTarget` and combines it with
  the given package targets to create a single active opaque target.
-/
def Package.buildDepTargetWith
(depTargets : Array (ActivePackageTarget i)) (self : Package) : BuildM ActiveOpaqueTarget := do
  let extraDepTarget ← self.extraDepTarget.run
  let depTarget ← ActiveTarget.collectOpaqueArray depTargets
  extraDepTarget.mixOpaqueAsync depTarget

/--
  Build an active package target after
  resolving the package's dependencies and recursively building them.

  To build each package, run the given `build` function on it,
  which takes the package and its building dependencies as arguments.
-/
def recBuildPackageWithDeps
[Monad m] [MonadLiftT BuildM m] [MonadStore Name (Array (ActivePackageTarget i)) m]
[Inhabited i] (build : Array (ActivePackageTarget i) → Package → BuildM (ActivePackageTarget i))
: RecBuild Package (Array (ActivePackageTarget i)) m := fun pkg buildPkg => do
  let mut depTargets := #[]
  for dep in pkg.dependencies do
    let targets? ← fetch? dep.name
    let targets ← do
      if let some targets := targets? then
        pure targets
      else
        let depPkg ← liftM (m := BuildM) <| resolveDep pkg dep
        buildPkg depPkg
    depTargets := depTargets ++ targets
  let pkgTarget ← build depTargets pkg
  depTargets.push pkgTarget

/--
  Build the  package along with its dependencies
  by using the given `build` function recursively.
-/
def Package.buildRec (self : Package) [Inhabited i]
(build : Array (ActivePackageTarget i) → Package → BuildM (ActivePackageTarget i))
: BuildM (ActivePackageTarget i) := do
  let recBuild := recBuildPackageWithDeps build
  let targets ← failOnBuildCycle <| ← RBTopT.run' <|
    buildRBTop (cmp := Name.quickCmp) recBuild Package.name self
  targets.back

/--
  Build an `Array` of `Package`s along with their dependencies
  by using the given `build` function recursively.
-/
def buildPackageArrayWithDeps (pkgs : Array Package) [Inhabited i]
(build : Array (ActivePackageTarget i) → Package → BuildM (ActivePackageTarget i))
: BuildM (Array (ActivePackageTarget i)) := do
  failOnBuildCycle <| ← RBTopT.run' <| pkgs.concatMapM fun pkg =>
    buildRBTop (cmp := Name.quickCmp) (recBuildPackageWithDeps build) Package.name pkg

/-- Build the dependencies of a package (as targets) using the given `build` function. -/
def Package.buildDepTargets [Inhabited i]
(build :  Array (ActivePackageTarget i) → Package → BuildM (ActivePackageTarget i)) (self : Package)
: BuildM (Array (ActivePackageTarget i)) := do
  buildPackageArrayWithDeps (← self.resolveDirectDeps) build


/--
   Build an active target for the package by
  running the given `RecModuleBuild` on the given root module.
-/
def Package.buildModuleDAGTarget [Inhabited i] (mod : Name)
(buildMod : RecModuleBuild i) (self : Package) : BuildM (ActivePackageTarget i) := do
  let (targetE, targetMap) ← RBTopT.run do
    buildRBTop buildMod id mod
  let target ← failOnBuildCycle targetE
  return target.withInfo ⟨self, targetMap⟩

/--
  Build an active target for the package by
  running the given `RecModuleBuild` on the given root modules.
-/
def Package.buildModulesDAGTarget [Inhabited i] (mods : Array Name)
(buildMod : RecModuleBuild i) (self : Package) : BuildM (ActivePackageTarget i) := do
  let (targetsE, targetMap) ← RBTopT.run do
    mods.mapM fun mod => buildRBTop buildMod id mod
  let targets ← failOnBuildCycle targetsE
  let target ← ActiveTarget.collectOpaqueArray targets
  return target.withInfo ⟨self, targetMap⟩

/--
  Build an active target for the package by
  running the given `RecModuleBuild` on each of its top-level modules
  (i.e., those specified in its `libGlobs` configuration).
-/
def Package.buildTarget [Inhabited i]
(buildMod : RecModuleBuild i) (self : Package) : BuildM (ActivePackageTarget i) := do
  self.buildModulesDAGTarget (← self.getModuleArray) buildMod

-- # Build Package Modules

def Package.buildOleanTargetWithDepTargets
(depTargets : Array (ActivePackageTarget FilePath)) (self : Package)
: BuildM (ActivePackageTarget FilePath) := do
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := packageTargetsToOleanDirs depTargets
  self.buildTarget <| self.recBuildModuleOleanTargetWithLocalImports moreOleanDirs depTarget

/-- Build the `.olean` and files of package and its dependencies' modules. -/
def Package.buildOleanTarget (self : Package) : BuildM (ActivePackageTarget FilePath) := do
  self.buildRec buildOleanTargetWithDepTargets

def Package.buildOleanAndCTargetWithDepTargets
(depTargets : Array (ActivePackageTarget OleanAndC)) (self : Package)
: BuildM (ActivePackageTarget OleanAndC) := do
  let depTarget ← self.buildDepTargetWith depTargets
  let moreOleanDirs := packageTargetsToOleanDirs depTargets
  self.buildTarget <| self.recBuildModuleOleanAndCTargetWithLocalImports moreOleanDirs depTarget

/-- Build the `.olean` and `.c` files of package and its dependencies' modules. -/
def Package.buildOleanAndCTarget (self : Package) : BuildM (ActivePackageTarget OleanAndC) := do
  self.buildRec buildOleanAndCTargetWithDepTargets

def Package.buildDepOleans (self : Package) : BuildM PUnit := do
  let targets ← self.buildDepTargets buildOleanTargetWithDepTargets
  targets.forM fun target => discard <| target.materialize

def Package.oleanTarget (self : Package) : PackageTarget :=
  Target.mk self do pure (← self.buildOleanTarget).task

def Package.build (self : Package) : BuildM PUnit := do
  discard (← self.buildOleanTarget).materialize

-- # Build Specific Modules of the Package

def Package.moduleOleanTarget (mod : Name) (self : Package) : FileTarget :=
  Target.mk (self.modToOlean mod) do
    let depTargets ← self.buildDepTargets buildOleanTargetWithDepTargets
    let depTarget ← self.buildDepTargetWith depTargets
    let moreOleanDirs := packageTargetsToOleanDirs depTargets
    let build := self.recBuildModuleOleanTargetWithLocalImports moreOleanDirs depTarget
    pure (← buildModuleTarget mod build).task

def Package.moduleOleanAndCTarget (mod : Name) (self : Package) : OleanAndCTarget :=
  Target.mk ⟨self.modToOlean mod, self.modToC mod⟩ do
    let depTargets ← self.buildDepTargets buildOleanAndCTargetWithDepTargets
    let depTarget ← self.buildDepTargetWith depTargets
    let moreOleanDirs := packageTargetsToOleanDirs depTargets
    let build := self.recBuildModuleOleanAndCTargetWithLocalImports moreOleanDirs depTarget
    pure (← buildModuleTarget mod build).task

-- # Build Imports

/-- Pick the local imports of the package from a list of import strings. -/
def Package.filterLocalImports
(imports : List String) (self : Package) : Array Name := do
  let mut localImports := #[]
  for imp in imports do
    let impName := imp.toName
    if self.isLocalModule impName then
      localImports := localImports.push impName
  return localImports

/-- Build the package's dependencies and a list of imports, returning the list of packages built. -/
def Package.buildImportsAndDeps
(imports : List String := []) (self : Package) : BuildM (List Package) := do
  -- resolve and build deps
  let depTargets ← self.buildDepTargets buildOleanTargetWithDepTargets
  let depTarget ← self.buildDepTargetWith depTargets
  let depPkgs := depTargets.map (·.package) |>.foldl (flip List.cons) []
  if imports.isEmpty then
    -- wait for deps to finish building
    discard depTarget.materialize
  else
     -- build local imports from list
    let moreOleanDirs := depPkgs.map (·.oleanDir)
    let localImports := self.filterLocalImports imports
    let build := self.recBuildModuleOleanTargetWithLocalImports moreOleanDirs depTarget
    let targets ← buildModuleTargets localImports build
    targets.forM (discard ·.materialize)
  return self :: depPkgs
