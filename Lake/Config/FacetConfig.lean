/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Info
import Lake.Build.Store

namespace Lake

/-- A facet's declarative configuration. -/
structure FacetConfig (DataFam : Name → Type u) (BuildFn : Type u → Type v) (name : Name) where
  /-- The type of the target's build result. -/
  resultType : Type u
  /-- The facet's build function. -/
  build : BuildFn resultType
  /-- Proof that the facet's build result data type is properly registered. -/
  data_eq_result : DataFam name = resultType
   /-- Is this facet a buildable target? -/
  result_eq_target? : Option <| PLift <| PSigma fun α => resultType = ActiveBuildTarget α

instance [(α : Type u) → Inhabited (BuildFn α)] : Inhabited (FacetConfig DataFam BuildFn name) := ⟨{
  resultType := DataFam name
  build := default
  data_eq_result := rfl
  result_eq_target? := none
}⟩

abbrev FacetBuildFn (ι) :=
  fun resultType => {m : Type → Type} →
    [Monad m] → [MonadLift BuildM m] → [MonadBuildStore m] →
    ι → IndexT m resultType

instance : Inhabited (FacetBuildFn ι α) :=
  ⟨fun _ => liftM (m := BuildM) failure⟩

namespace FacetConfig

protected def name (_ : FacetConfig DataFam BuildFn name) :=
  name

instance (cfg : FacetConfig Fam Fn name) :
  FamilyDef Fam cfg.name cfg.resultType := ⟨cfg.data_eq_result⟩

def familyDef (cfg : FacetConfig Fam Fn name) : FamilyDef Fam name cfg.resultType :=
  ⟨cfg.data_eq_result⟩

def familyDefTarget (cfg : FacetConfig Fam Fn name)
(h : cfg.resultType = ActiveBuildTarget α) : FamilyDef Fam name (ActiveBuildTarget α) :=
  ⟨h ▸ cfg.data_eq_result⟩

end FacetConfig

/-- A dependently typed configuration based on its registered name. -/
structure NamedConfigDecl (β : Name → Type u) where
  name : Name
  config : β name

--------------------------------------------------------------------------------

/-- A module facet's declarative configuration. -/
abbrev ModuleFacetConfig := FacetConfig ModuleData (FacetBuildFn Module)
hydrate_opaque_type OpaqueModuleFacetConfig ModuleFacetConfig name

/-- A module facet declaration from a configuration file. -/
abbrev ModuleFacetDecl := NamedConfigDecl ModuleFacetConfig

--------------------------------------------------------------------------------

/-- A package facet's declarative configuration. -/
abbrev PackageFacetConfig := FacetConfig PackageData (FacetBuildFn Package)
hydrate_opaque_type OpaquePackageFacetConfig PackageFacetConfig name

/-- A package facet declaration from a configuration file. -/
abbrev PackageFacetDecl := NamedConfigDecl PackageFacetConfig
