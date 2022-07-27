/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Mario Carneiro
-/
import Lake.Build.Info
import Lake.Build.Store

namespace Lake

/-- A facet's declarative configuration. -/
structure FacetConfig (DataFam : Name → Type) (ι : Type) (name : Name) : Type where
  /-- The facet's build (function). -/
  build : ι → IndexBuildM (DataFam name)
  /-- Does this facet produce an associated asynchronous job? -/
  getJob? : Option (DataFam name → Job Unit)
  deriving Inhabited

protected abbrev FacetConfig.name (_ : FacetConfig DataFam ι name) := name

/-- A smart constructor for facet configurations that are not known to generate targets. -/
@[inline] def mkFacetConfig (build : ι → IndexBuildM α)
[h : FamilyDef Fam facet α] : FacetConfig Fam ι facet where
  build := cast (by rw [← h.family_key_eq_type]) build
  getJob? := none

/-- A smart constructor for facet configurations that generate jobs for the CLI. -/
@[inline] def mkFacetJobConfig (build : ι → IndexBuildM (BuildJob α))
[h : FamilyDef Fam facet (BuildJob α)] : FacetConfig Fam ι facet where
  build := cast (by rw [← h.family_key_eq_type]) build
  getJob? := some fun data => discard <| ofFamily data

/-- A dependently typed configuration based on its registered name. -/
structure NamedConfigDecl (β : Name → Type u) where
  name : Name
  config : β name

/-- A module facet's declarative configuration. -/
abbrev ModuleFacetConfig := FacetConfig ModuleData Module

/-- A module facet declaration from a configuration file. -/
abbrev ModuleFacetDecl := NamedConfigDecl ModuleFacetConfig

/-- A package facet's declarative configuration. -/
abbrev PackageFacetConfig := FacetConfig PackageData Package

/-- A package facet declaration from a configuration file. -/
abbrev PackageFacetDecl := NamedConfigDecl PackageFacetConfig

/-- A library facet's declarative configuration. -/
abbrev LibraryFacetConfig := FacetConfig LibraryData LeanLib

/-- A library facet declaration from a configuration file. -/
abbrev LibraryFacetDecl := NamedConfigDecl LibraryFacetConfig
