/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Fetch

namespace Lake
open Lean (Name)

/-- A custom target's declarative configuration. -/
structure TargetConfig (pkgName name : Name) : Type where
  /-- The target's build function. -/
  build : (pkg : NPackage pkgName) → FetchM (CustomData (pkgName, name))
  /-- The target's resulting build job. -/
  getJob : CustomData (pkgName, name) → BuildJob Unit
  deriving Inhabited

/-- A smart constructor for target configurations that generate CLI targets. -/
@[inline] def mkTargetJobConfig
(build : (pkg : NPackage pkgName) → FetchM (BuildJob α))
[h : FamilyOut CustomData (pkgName, name) (BuildJob α)] : TargetConfig pkgName name where
  build := cast (by rw [← h.family_key_eq_type]) build
  getJob := fun data => discard <| ofFamily data

/-- A dependently typed configuration based on its registered package and name. -/
structure TargetDecl where
  pkg : Name
  name : Name
  config : TargetConfig pkg name

hydrate_opaque_type OpaqueTargetConfig TargetConfig pkgName name

/-- Try to find a target configuration in the package with the given name . -/
def Package.findTargetConfig? (name : Name) (self : Package) : Option (TargetConfig self.name name) :=
  self.opaqueTargetConfigs.find? name |>.map (·.get)
