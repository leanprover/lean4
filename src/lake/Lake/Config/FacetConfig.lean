/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone, Mario Carneiro
-/
module

prelude
public import Lake.Build.Fetch

namespace Lake
open Lean (Name)

/-- A facet's declarative configuration. -/
public structure FacetConfig (name : Name) : Type where
  /-- The facet kind (i.e., the kind of targets that support this facet). -/
  kind : Name
  /-- The facet's fetch function. -/
  fetchFn : DataType kind → FetchM (Job (FacetOut name))
  /-- The optional data kind of the facet's output. -/
  [outKind : OptDataKind (FacetOut name)]
  /-- Is this facet compatible with the `lake build` CLI? -/
  buildable : Bool := true
  /-- Format this facet's output (e.g., for `lake query`). -/
  format : OutFormat → FacetOut name → String
  /-- Whether the fetch of this facet should be cached in the Lake build store. -/
  memoize : Bool := true
  deriving Inhabited

public protected abbrev FacetConfig.name (_ : FacetConfig name) := name

public structure KFacetConfig (k : Name) (name : Name) extends FacetConfig name where
  kind := k
  kind_eq : toFacetConfig.kind = k := by rfl

public abbrev FacetConfig.toKind
  {kind : Name} (self : FacetConfig name) (h : self.kind = kind)
: KFacetConfig kind name := KFacetConfig.mk self h

public def FacetConfig.toKind? (kind : Name) (self : FacetConfig name) : Option (KFacetConfig kind name) :=
  if h : self.kind = kind then
    some (self.toKind h)
  else
    none

/-- Run the facet configuration's fetch function. -/
@[inline] public def KFacetConfig.run
  [FamilyOut DataType kind α]
  [FamilyOut FacetOut facet β]
  (self : KFacetConfig kind facet) (info : α)
: FetchM (Job β) :=
  cast (by simp) <| self.fetchFn <| cast (by simp [self.kind_eq]) info

/-- A smart constructor for facet configurations that generate jobs for the CLI. -/
@[inline] public def mkFacetJobConfig
  [FormatQuery β]
  [outKind : OptDataKind β]
  [i : FamilyOut DataType kind α]
  [o : FamilyOut FacetOut facet β]
  (build : α → FetchM (Job β))
  (buildable := true) (memoize := true)
: KFacetConfig kind facet where
  buildable; memoize
  outKind := o.fam_eq ▸ outKind
  fetchFn := i.fam_eq ▸ o.fam_eq ▸ build
  format := o.fam_eq ▸ formatQuery

/-- A dependently typed configuration based on its registered name. -/
public structure NamedConfigDecl (β : Name → Type u) where
  name : Name
  config : β name

/-- A module facet's declarative configuration. -/
public abbrev ModuleFacetConfig := KFacetConfig Module.facetKind

/-- A module facet declaration from a configuration file. -/
public abbrev ModuleFacetDecl := NamedConfigDecl ModuleFacetConfig

/-- A package facet's declarative configuration. -/
public abbrev PackageFacetConfig := KFacetConfig Package.facetKind

/-- A package facet declaration from a configuration file. -/
public abbrev PackageFacetDecl := NamedConfigDecl PackageFacetConfig

/-- A library facet's declarative configuration. -/
public abbrev LibraryFacetConfig := KFacetConfig LeanLib.facetKind

/-- A library facet declaration from a configuration file. -/
public abbrev LibraryFacetDecl := NamedConfigDecl LibraryFacetConfig

public instance : TypeName ModuleFacetDecl := unsafe (.mk _ ``ModuleFacetDecl)
public instance : TypeName PackageFacetDecl := unsafe (.mk _ ``PackageFacetDecl)
public instance : TypeName LibraryFacetDecl := unsafe (.mk _ ``LibraryFacetDecl)

/-- A library facet's declarative configuration. -/
public abbrev LeanLibFacetConfig := LibraryFacetConfig

/-- A Lean executable facet's declarative configuration. -/
public abbrev LeanExeFacetConfig := KFacetConfig LeanExe.facetKind

/-- An external library facet's declarative configuration. -/
public abbrev ExternLibFacetConfig := KFacetConfig ExternLib.facetKind
