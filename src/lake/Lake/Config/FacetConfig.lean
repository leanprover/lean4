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
structure FacetConfig (kind name : Name) : Type where
  /-- The facet's fetch function. -/
  fetchFn : TargetData kind → FetchM (Job (FacetData kind name))
  /-- Is this facet compatible with the `lake build` CLI? -/
  buildable : Bool := true
  /-- Format this facet's output (e.g., for `lake query`). -/
  format : OutFormat → FacetData kind name → String
  deriving Inhabited

protected abbrev FacetConfig.name (_ : FacetConfig kind name) := name

/-- Run the facet configuration's fetch function. -/
@[inline] def FacetConfig.run
  [FamilyOut TargetData kind α]
  [FamilyOut (FacetData kind) facet β]
  (self : FacetConfig kind facet) (info : α)
: FetchM (Job β) :=
  cast (by simp) <| self.fetchFn <| toFamily info

/-- A smart constructor for facet configurations that generate jobs for the CLI. -/
@[inline] def mkFacetJobConfig
  [FormatQuery β]
  [i : FamilyOut TargetData kind α]
  [o : FamilyOut (FacetData kind) facet β]
  (build : α → FetchM (Job β)) (buildable := true)
: FacetConfig kind facet where
  buildable
  fetchFn := i.fam_eq ▸ o.fam_eq ▸ build
  format := o.fam_eq ▸ formatQuery

/-- A two layer kind-name-configuration map of facets. -/
abbrev FacetMap := DNameMap fun k => (DNameMap (FacetConfig k))
@[inline] def FacetMap.empty : FacetMap := DNameMap.empty

/-- A dependently typed configuration based on its registered name. -/
structure NamedConfigDecl (β : Name → Type u) where
  name : Name
  config : β name

/-- A module facet's declarative configuration. -/
abbrev ModuleFacetConfig := FacetConfig Module.facetKind

/-- A module facet declaration from a configuration file. -/
abbrev ModuleFacetDecl := NamedConfigDecl ModuleFacetConfig

/-- A package facet's declarative configuration. -/
abbrev PackageFacetConfig := FacetConfig Package.facetKind

/-- A package facet declaration from a configuration file. -/
abbrev PackageFacetDecl := NamedConfigDecl PackageFacetConfig

/-- A library facet's declarative configuration. -/
abbrev LibraryFacetConfig := FacetConfig LeanLib.facetKind

/-- A library facet declaration from a configuration file. -/
abbrev LibraryFacetDecl := NamedConfigDecl LibraryFacetConfig

deriving instance TypeName for
  ModuleFacetDecl, PackageFacetDecl, LibraryFacetDecl

/-- A library facet's declarative configuration. -/
abbrev LeanLibFacetConfig := LibraryFacetConfig

/-- A Lean executable facet's declarative configuration. -/
abbrev LeanExeFacetConfig := FacetConfig LeanExe.facetKind

/-- An external library facet's declarative configuration. -/
abbrev ExternLibFacetConfig := FacetConfig ExternLib.facetKind
