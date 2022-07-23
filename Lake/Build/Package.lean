/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index

namespace Lake

/-- Compute a topological ordering of the package's transitive dependencies. -/
def Package.recComputeDeps (self : Package) : IndexBuildM (Array Package) := do
  let mut deps := #[]
  let mut depSet := PackageSet.empty
  for dep in self.deps do
    for depDep in (← recBuild <| dep.facet `deps) do
      unless depSet.contains depDep do
        deps := deps.push depDep
        depSet := depSet.insert depDep
    unless depSet.contains dep do
      deps := deps.push dep
      depSet := depSet.insert dep
  return deps

/-- The `PackageFacetConfig` for the builtin `depsFacet`. -/
def Package.depsFacetConfig : PackageFacetConfig depsFacet :=
  mkFacetConfig (·.recComputeDeps)

/-- Build the `extraDepTarget` for the package and its transitive dependencies. -/
def Package.recBuildExtraDepTargets (self : Package) : IndexBuildM ActiveOpaqueTarget := do
  let mut target := ActiveTarget.nil
  for dep in self.deps do
    target ← target.mixOpaqueAsync (← dep.extraDep.recBuild)
  target.mixOpaqueAsync <| ← self.extraDepTarget.activate

/-- The `PackageFacetConfig` for the builtin `dynlibFacet`. -/
def Package.extraDepFacetConfig : PackageFacetConfig extraDepFacet :=
  mkFacetTargetConfig (·.recBuildExtraDepTargets)

open Package in
/--
A package facet name to build function map that contains builders for
the initial set of Lake package facets (e.g., `extraDep`).
-/
def initPackageFacetConfigs : DNameMap PackageFacetConfig :=
  DNameMap.empty
  |>.insert depsFacet depsFacetConfig
  |>.insert extraDepFacet extraDepFacetConfig
