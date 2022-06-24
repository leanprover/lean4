
/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Index

open Std Lean
namespace Lake

-- # Index Recursive Build

section
variable [Monad m] [MonadLiftT BuildM m] [MonadBuildStore m]

/--
Build the module's specified facet recursively using a topological-based
scheduler, storing the results in the monad's store and returning the result
of the top-level build.
-/
@[inline] def buildModuleTop (mod : Module) (facet : WfName)
[h : DynamicType ModuleData facet α] : CycleT BuildKey m α  :=
  have of_data := by unfold BuildData, BuildInfo.key; simp [h.eq_dynamic_type]
  cast of_data <| buildIndexTop (m := m) <| BuildInfo.module mod facet

/--
Build the module's specified facet recursively using a topological-based
scheduler, storing the results in the monad's store and returning nothing.
-/
@[inline] def buildModuleTop' (mod : Module) (facet : WfName) : CycleT BuildKey m PUnit :=
  discard <| buildIndexTop (m := m) <| BuildInfo.module mod facet

end

-- # Module Facet Builders

/--
Recursively build the specified facet of the given module,
returning the result.
-/
def buildModuleFacet
(mod : Module) (facet : WfName)
[DynamicType ModuleData facet α] : BuildM α := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty do
    buildModuleTop mod facet

/--
Recursively build the specified facet of each module,
returning an `Array`  of the results.
-/
def buildModuleFacetArray
(mods : Array Module) (facet : WfName)
[DynamicType ModuleData facet α] : BuildM (Array α) := do
  failOnBuildCycle <| ← EStateT.run' BuildStore.empty <| mods.mapM fun mod =>
    buildModuleTop mod facet

/--
Recursively build the specified facet of the given module,
returning the resulting map of built modules and their results.
-/
def buildModuleFacetMap
(mods : Array Module) (facet : WfName)
[DynamicType ModuleData facet α] : BuildM (NameMap α) := do
  let (x, bStore) ← EStateT.run BuildStore.empty <| mods.forM fun mod =>
    buildModuleTop' mod facet
  failOnBuildCycle x
  return bStore.collectModuleFacetMap facet

-- # Module Facet Targets

def Module.facetTarget (facet : WfName) (self : Module)
[DynamicType ModuleData facet (ActiveBuildTarget α)] : OpaqueTarget :=
  BuildTarget.mk' () do return (← buildModuleFacet self facet).task

@[inline] def Module.oleanTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean |>.withInfo self.oleanFile

@[inline] def Module.ileanTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean  |>.withInfo self.ileanFile

@[inline] def Module.cTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean.c |>.withInfo self.cFile

@[inline] def Module.oTarget (self : Module) : FileTarget :=
  self.facetTarget &`lean.o |>.withInfo self.oFile
