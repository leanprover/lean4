/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Mario Carneiro
-/
prelude
import Lake.Build.Fetch
import Lake.Config.OutFormat

namespace Lake
open Lean (Name)

/-- A facet's declarative configuration. -/
structure FacetConfig (DataFam : Name → Type) (ι : Type) (name : Name) : Type where
  /-- The facet's build (function). -/
  build : ι → FetchM (DataFam name)
  /-- The facet's associated asynchronous job (e.g., for `lake build`). -/
  getBuildJob? : Option (DataFam name → BuildJob Unit)
  /-- The facet's build job with formatted output (e.g., for `lake fetch`). -/
  getFetchJob? : Option (OutFormat → DataFam name → BuildJob String)
  deriving Inhabited

protected abbrev FacetConfig.name (_ : FacetConfig DataFam ι name) := name

/--
A smart constructor for facet configurations
that are not known to generate targets. -/
@[inline] def mkFacetConfig
  (build : ι → FetchM α) [h : FamilyOut Fam facet α]
: FacetConfig Fam ι facet where
  build := cast (by rw [← h.family_key_eq_type]) build
  getBuildJob? := none
  getFetchJob? := none

/-- A smart constructor for facet configurations that generate jobs for the CLI. -/
@[inline] def mkFacetJobConfig
  (build : ι → FetchM (BuildJob α)) [h : FamilyOut Fam facet (BuildJob α)]
: FacetConfig Fam ι facet where
  build := cast (by rw [← h.family_key_eq_type]) build
  getBuildJob? := some fun data => discard <| ofFamily data
  getFetchJob? := none

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
