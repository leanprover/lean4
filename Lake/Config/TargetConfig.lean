/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Info
import Lake.Build.Store

namespace Lake

/-- A custom target's declarative configuration. -/
structure TargetConfig where
  /-- The name of the target. -/
  name : WfName
  /-- The type of the target's build result. -/
  resultType : Type
  /-- The target's build function. -/
  build : {m : Type → Type} →
    [Monad m] → [MonadLift BuildM m] → [MonadBuildStore m] →
    Package → IndexT m (ActiveBuildTarget resultType)
  /-- Proof that target's build result is the correctly typed target.-/
  data_eq_target : CustomData name = ActiveBuildTarget resultType

custom_data _nil_ : ActiveOpaqueTarget

instance : Inhabited TargetConfig := ⟨{
  name := &`_nil_
  resultType := PUnit
  build := default
  data_eq_target := eq_dynamic_type
}⟩

hydrate_opaque_type OpaqueTargetConfig TargetConfig

instance dynamicTypeOfTargetConfig {cfg : TargetConfig}
: DynamicType CustomData cfg.name (ActiveBuildTarget cfg.resultType) :=
  ⟨cfg.data_eq_target⟩

/-- Try to find a target configuration in the package with the given name . -/
def Package.findTargetConfig? (name : Name) (self : Package) : Option TargetConfig :=
  self.opaqueTargetConfigs.find? name |>.map (·.get)
