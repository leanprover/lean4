/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Fetch
import Lake.Config.OutFormat

open Lean

namespace Lake

/-- A custom target's declarative configuration. -/
structure TargetConfig (pkgName name : Name) : Type where
  /-- The target's fetch function. -/
  fetchFn : (pkg : NPackage pkgName) → FetchM (Job (CustomData (pkgName, name)))
  /-- Format the target's output (e.g., for `lake query`). -/
  format : OutFormat → CustomData (pkgName, name) → String
  deriving Inhabited

/-- A smart constructor for target configurations that generate CLI targets. -/
@[inline] def mkTargetJobConfig
  [FormatQuery α] [h : FamilyOut CustomData (pkgName, name) α]
  (fetch : (pkg : NPackage pkgName) → FetchM (Job α))
: TargetConfig pkgName name where
  fetchFn := h.family_key_eq_type ▸ fetch
  format := h.family_key_eq_type ▸ formatQuery

/-- A dependently typed configuration based on its registered package and name. -/
structure TargetDecl where
  pkg : Name
  name : Name
  config : TargetConfig pkg name

hydrate_opaque_type OpaqueTargetConfig TargetConfig pkgName name

/-- Try to find a target configuration in the package with the given name . -/
def Package.findTargetConfig? (name : Name) (self : Package) : Option (TargetConfig self.name name) :=
  self.opaqueTargetConfigs.find? name |>.map (·.get)
