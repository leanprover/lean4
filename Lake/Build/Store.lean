/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Data
import Lake.Util.StoreInsts

/-!
# The Lake Build Store

The Lake build store is the map of Lake build keys to build task and/or
build results that is slowly filled during a recursive build (e.g., via
topological-based build of an initial key's dependencies).
-/

namespace Lake

/-- The type of the Lake build store. -/
abbrev BuildStore :=
  DRBMap BuildKey BuildData BuildKey.quickCmp

@[inline] def BuildStore.empty : BuildStore := DRBMap.empty

/-- A monad equipped with a Lake build store. -/
abbrev MonadBuildStore (m) := MonadDStore BuildKey BuildData m

instance (k : ModuleBuildKey f)
[t : DynamicType ModuleData f α] : DynamicType BuildData k α where
  eq_dynamic_type := by
    unfold BuildData
    simp [k.is_module_key, k.facet_eq_fixed, t.eq_dynamic_type]

@[inline] instance [MonadBuildStore m]
[DynamicType ModuleData f α] : MonadStore (ModuleBuildKey f) α m where
  fetch? k := fetch? k.toBuildKey
  store k a := store k.toBuildKey a

instance (k : PackageBuildKey f)
[t : DynamicType PackageData f α] : DynamicType BuildData k α where
  eq_dynamic_type := by
    unfold BuildData, BuildKey.isModuleKey
    have has_pkg := of_decide_eq_true (of_decide_eq_true k.is_package_key |>.1)
    simp [has_pkg, k.is_package_key, k.facet_eq_fixed, t.eq_dynamic_type]

@[inline] instance [MonadBuildStore m]
[DynamicType PackageData f α] : MonadStore (PackageBuildKey f) α m where
  fetch? k := fetch? k.toBuildKey
  store k a := store k.toBuildKey a
