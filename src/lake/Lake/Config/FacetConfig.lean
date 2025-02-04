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
  /-- The facet's fetch function. -/
  fetchFn : ι → FetchM (Job (DataFam name))
  /-- Is this facet compatible with the `lake build` CLI? -/
  buildable : Bool := true
  /-- Format this facet's output (e.g., for `lake query`). -/
  format : OutFormat → DataFam name → String
  deriving Inhabited

protected abbrev FacetConfig.name (_ : FacetConfig DataFam ι name) := name

/-- A smart constructor for facet configurations that generate jobs for the CLI. -/
@[inline] def mkFacetJobConfig
  [FormatQuery α] [h : FamilyOut Fam facet α]
  (build : ι → FetchM (Job α)) (buildable := true)
: FacetConfig Fam ι facet where
  buildable
  fetchFn := h.family_key_eq_type ▸ build
  format := h.family_key_eq_type ▸ formatQuery

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
