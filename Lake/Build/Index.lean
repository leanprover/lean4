/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Module1
import Lake.Build.LeanTarget1
import Lake.Build.Topological
import Lake.Util.EStateT

/-!
# The Lake Build Index

The Lake build index is the complete map of Lake build keys to
Lake build functions, which is used by Lake to build any Lake build info.

This module contains the definitions used to formalize this concept,
and it leverages the index to perform topological-based recursive builds.
-/

open Std Lean
namespace Lake

/-!
## Facet Build Maps
-/

/-- A map from module facet names to build functions. -/
abbrev ModuleBuildMap (m : Type → Type v) :=
  DRBMap WfName (cmp := WfName.quickCmp) fun k =>
    Module → IndexBuildFn m → m (ModuleData k)

@[inline] def ModuleBuildMap.empty : ModuleBuildMap m := DRBMap.empty

/-- A map from package facet names to build functions. -/
abbrev PackageBuildMap (m : Type → Type v) :=
  DRBMap WfName (cmp := WfName.quickCmp) fun k =>
    Package → IndexBuildFn m → m (PackageData k)

@[inline] def PackageBuildMap.empty : PackageBuildMap m := DRBMap.empty

/-- A map from target facet names to build functions. -/
abbrev TargetBuildMap (m : Type → Type v) :=
  DRBMap WfName (cmp := WfName.quickCmp) fun k =>
    Package → IndexBuildFn m → m (PackageData k)

@[inline] def TargetBuildMap.empty : PackageBuildMap m := DRBMap.empty

/-!
## Build Function Constructor Helpers
-/

/--
Converts a conveniently typed module facet build function into its
dynamically typed equivalent.
-/
@[inline] def mkModuleFacetBuild {facet : WfName} (build : Module → IndexT m α)
[h : DynamicType ModuleData facet α] : Module → IndexT m (ModuleData facet) :=
  cast (by rw [← h.eq_dynamic_type]) build

/--
Converts a conveniently typed package facet build function into its
dynamically typed equivalent.
-/
@[inline] def mkPackageFacetBuild {facet : WfName} (build : Package → IndexT m α)
[h : DynamicType PackageData facet α] : Package → IndexT m (PackageData facet) :=
  cast (by rw [← h.eq_dynamic_type]) build

/--
Converts a conveniently typed target build function into its
dynamically typed equivalent.
-/
@[inline] def mkTargetBuild (facet : WfName) (build : IndexT m α)
[h : DynamicType TargetData facet α] : IndexT m (TargetData facet) :=
  cast (by rw [← h.eq_dynamic_type]) build

section
variable [Monad m] [MonadLiftT BuildM m] [MonadBuildStore m]

/-!
## Initial Facet Maps
-/

/--
A module facet name to build function map that contains builders for
the initial set of Lake module facets (e.g., `lean.{imports, c, o, dynlib]`).
-/
@[specialize] def moduleBuildMap : ModuleBuildMap m :=
  have : MonadLift BuildM m := ⟨liftM⟩
  ModuleBuildMap.empty (m := m)
  -- Compute unique imports (direct × transitive)
  |>.insert &`lean.imports (mkModuleFacetBuild (·.recParseImports))
  -- Build module (`.olean` and `.ilean`)
  |>.insert &`lean (mkModuleFacetBuild (fun mod => do
    mod.recBuildLean !mod.isLeanOnly
  ))
  |>.insert &`olean (mkModuleFacetBuild (fun mod => do
    mod.recBuildLean (!mod.isLeanOnly) <&> (·.withInfo mod.oleanFile)
  ))
  |>.insert &`ilean (mkModuleFacetBuild (fun mod => do
    mod.recBuildLean (!mod.isLeanOnly) <&> (·.withInfo mod.ileanFile)
  ))
  -- Build module `.c` (and `.olean` and `.ilean`)
  |>.insert &`lean.c (mkModuleFacetBuild <| fun mod => do
    mod.recBuildLean true <&> (·.withInfo mod.cFile)
  )
  -- Build module `.o`
  |>.insert &`lean.o (mkModuleFacetBuild <| fun mod => do
    let cTarget ← mod.recBuildFacet &`lean.c
    mod.mkOTarget (Target.active cTarget) |>.activate
  )
  -- Build shared library for `--load-dynlb`
  |>.insert &`lean.dynlib (mkModuleFacetBuild (·.recBuildDynLib))

/--
A package facet name to build function map that contains builders for
the initial set of Lake package facets (e.g., `extraDep`).
-/
@[specialize] def packageBuildMap : PackageBuildMap m :=
  have : MonadLift BuildM m := ⟨liftM⟩
  PackageBuildMap.empty (m := m)
  -- Compute the package's transitive dependencies
  |>.insert &`deps (mkPackageFacetBuild <| fun pkg => do
    let mut deps := #[]
    let mut depSet := PackageSet.empty
    for dep in pkg.dependencies do
      if let some depPkg ← findPackage? dep.name then
        for depDepPkg in (← depPkg.recBuildFacet &`deps) do
          unless depSet.contains depDepPkg do
            deps := deps.push depDepPkg
            depSet := depSet.insert depDepPkg
        unless depSet.contains depPkg do
          deps := deps.push depPkg
          depSet := depSet.insert depPkg
    return deps
  )
  -- Build the `extraDepTarget` for the package and its transitive dependencies
  |>.insert &`extraDep (mkPackageFacetBuild <| fun pkg => do
    let mut target := ActiveTarget.nil
    for dep in pkg.dependencies do
      if let some depPkg ← findPackage? dep.name then
        let extraDepTarget ← depPkg.recBuildFacet &`extraDep
        target ← target.mixOpaqueAsync extraDepTarget
    target.mixOpaqueAsync <| ← pkg.extraDepTarget.activate
  )
/-!
## Topologically-based Recursive Build Using the Index
-/

/-- Recursive build function for anything in the Lake build index. -/
@[specialize] def recBuildIndex (info : BuildInfo) : IndexT m (BuildData info.key) := do
  have : MonadLift BuildM m := ⟨liftM⟩
  match info with
  | .module mod facet =>
    if let some build := moduleBuildMap.find? facet then
      build mod
    else
      error s!"do not know how to build module facet `{facet}`"
  | .package pkg facet =>
    if let some build := packageBuildMap.find? facet then
      build pkg
    else
      error s!"do not know how to build package facet `{facet}`"
  | .staticLeanLib lib =>
    mkTargetBuild &`leanLib.static lib.recBuildStatic
  | .sharedLeanLib lib =>
    mkTargetBuild &`leanLib.shared lib.recBuildShared
  | .leanExe exe =>
    mkTargetBuild &`leanExe exe.recBuild
  | .staticExternLib lib =>
    mkTargetBuild &`externLib.static <| lib.target.activate
  | .sharedExternLib lib =>
    mkTargetBuild &`externLib.shared <| staticToLeanDynlibTarget (lib.target) |>.activate
  | _ =>
    error s!"do not know how to build `{info.key}`"

/--
Recursively build the given info using the Lake build index
and a topological / suspending scheduler.
-/
@[specialize] def buildIndexTop (info : BuildInfo) : CycleT BuildKey m (BuildData info.key) :=
  buildDTop BuildData BuildInfo.key recBuildIndex info

/--
Build the package's specified facet recursively using a topological-based
scheduler, storing the results in the monad's store and returning the result
of the top-level build.
-/
@[inline] def buildPackageTop (pkg : Package) (facet : WfName)
[h : DynamicType PackageData facet α] : CycleT BuildKey m α  :=
  have of_data := by
    unfold BuildData, BuildInfo.key, Package.mkBuildKey
    simp [h.eq_dynamic_type]
  cast of_data <| buildIndexTop (m := m) <| BuildInfo.package pkg facet

end

/-!
## Package Facet Builders
-/

/--
Recursively build the specified facet of the given package,
returning the result.
-/
def Package.buildFacet (self : Package) (facet : WfName)
[DynamicType PackageData facet α] : BuildM α := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty do
    buildPackageTop self facet
