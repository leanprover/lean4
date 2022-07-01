/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Info
import Lake.Build.Store

namespace Lake

/-- A package facet's declarative configuration. -/
structure PackageFacetConfig where
  /-- The name of the target. -/
  name : WfName
  /-- The type of the target's build result. -/
  resultType : Type
  /-- The target's build function. -/
  build : {m : Type → Type} →
    [Monad m] → [MonadLift BuildM m] → [MonadBuildStore m] →
    Package → IndexT m (ActiveBuildTarget resultType)
  /-- Proof that target's build result is the correctly typed target.-/
  data_eq_target : PackageData name = ActiveBuildTarget resultType

instance : Inhabited PackageFacetConfig := ⟨{
  name := &`extraDep
  resultType := PUnit
  build := default
  data_eq_target := eq_dynamic_type
}⟩

hydrate_opaque_type OpaquePackageFacetConfig PackageFacetConfig

instance (cfg : PackageFacetConfig)
: DynamicType PackageData cfg.name (ActiveBuildTarget cfg.resultType) :=
  ⟨cfg.data_eq_target⟩

/-- Try to find a package configuration in the package with the given name . -/
def Package.findPackageFacetConfig? (name : Name) (self : Package) : Option PackageFacetConfig :=
  self.opaquePackageFacetConfigs.find? name |>.map (·.get)
