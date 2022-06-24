/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Data
import Lake.Config.Module
import Lake.Util.EquipT

namespace Lake

-- # Build Key Constructor Helpers

@[inline] def Module.mkBuildKey (facet : WfName) (self : Module) : ModuleBuildKey facet :=
  ⟨⟨none, self.name, facet⟩, rfl, rfl⟩

@[inline] def Package.mkBuildKey (facet : WfName) (self : Package) : PackageBuildKey facet :=
  ⟨⟨self.name, none, facet⟩, rfl, rfl⟩

-- # Build Info

/-- The type of Lake's build info. -/
inductive BuildInfo
| module (module : Module) (facet : WfName)
| package (package : Package) (facet : WfName)
| target (package : Package) (target : WfName) (facet : WfName)

def BuildInfo.key : (self : BuildInfo) → BuildKey
| module m f => ⟨none, m.name, f⟩
| package p f => ⟨p.name, none, f⟩
| target p t f => ⟨p.name, t, f⟩

/-- A build function for any element of the Lake build index. -/
abbrev IndexBuildFn (m : Type → Type v) :=
  -- `DBuildFn BuildInfo (BuildData ·.key) m` with less imports
  (info : BuildInfo) → m (BuildData info.key)

/-- A transformer to equip a monad with a build function for the Lake index. -/
abbrev IndexT (m : Type → Type v) := EquipT (IndexBuildFn m) m

@[inline] def Module.recBuildFacet (mod : Module) (facet : WfName)
[DynamicType ModuleData facet α] : IndexT m α := fun build =>
  let to_data := by unfold BuildData, BuildInfo.key; simp [eq_dynamic_type]
  cast to_data <| build <| BuildInfo.module mod facet

@[inline] def Package.recBuildFacet (pkg : Package) (facet : WfName)
[DynamicType PackageData facet α] : IndexT m α := fun build =>
  let to_data := by unfold BuildData, BuildInfo.key; simp [eq_dynamic_type]
  cast to_data <| build <| BuildInfo.package pkg facet

-- # Data Types of Build Results

/-- Lean binary build (`olean`, `ilean` files) -/
module_data lean : ActiveOpaqueTarget

/-- The `olean` file produced by `lean`  -/
module_data olean : ActiveOpaqueTarget

/-- The `ilean` file produced by `lean` -/
module_data ilean : ActiveOpaqueTarget

/-- The C file built from the Lean file via `lean` -/
module_data lean.c : ActiveFileTarget

/-- The object file built from `lean.c` -/
module_data lean.o : ActiveFileTarget

/-- Shared library for `--load-dynlib` -/
module_data lean.dynlib : ActiveFileTarget

/-- The direct × transitive imports of the Lean module. -/
module_data lean.imports : Array Module × Array Module

/-- The package's `extraDepTarget`. -/
package_data extraDep : ActiveOpaqueTarget
