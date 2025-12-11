/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake.Build.Fetch
meta import all Lake.Util.OpaqueType

open Lean

namespace Lake

/-- A custom target's declarative configuration. -/
public structure TargetConfig (pkgName name : Name) : Type where
  /-- The target's fetch function. -/
  fetchFn : (pkg : NPackage pkgName) → FetchM (Job (CustomData pkgName name))
  /-- Format the target's output (e.g., for `lake query`). -/
  format : OutFormat → CustomData pkgName name → String
  deriving Inhabited

/-- A smart constructor for target configurations that generate CLI targets. -/
@[inline] public def mkTargetJobConfig
  [FormatQuery α] [h : FamilyOut (CustomData pkgName) name α]
  (fetch : (pkg : NPackage pkgName) → FetchM (Job α))
: TargetConfig pkgName name where
  fetchFn := h.fam_eq ▸ fetch
  format := h.fam_eq ▸ formatQuery

public hydrate_opaque_type OpaqueTargetConfig TargetConfig pkgName name

@[inline] public def NConfigDecl.targetConfig (self : NConfigDecl p n) (h : self.kind.isAnonymous) : TargetConfig p n :=
  self.opaqueTargetConfig h |>.get

@[inline] public def NConfigDecl.targetConfig? (self : NConfigDecl p n) : Option (TargetConfig p n) :=
  self.opaqueTargetConfig?.map (·.get)

/-- A dependently typed configuration based on its registered package and name. -/
public abbrev TargetDecl := KConfigDecl .anonymous

/-- Try to find a target configuration in the package with the given name . -/
public def Package.findTargetConfig? (name : Name) (self : Package) : Option (TargetConfig self.keyName name) :=
  self.targetDeclMap.get? name |>.bind (·.targetConfig?)
