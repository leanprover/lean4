/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Util.Opaque

namespace Lake

/-- Opaque reference to a `Package` used for forward declaration. -/
declare_opaque_type OpaquePackage

/-- Opaque reference to a `Workspace` used for forward declaration. -/
declare_opaque_type OpaqueWorkspace

/-- Opaque reference to a `ModuleFacetConfig` used for forward declaration. -/
declare_opaque_type OpaqueModuleFacetConfig

/-- Opaque reference to a `PackageFacetConfig` used for forward declaration. -/
declare_opaque_type OpaquePackageFacetConfig

/-- Opaque reference to a `TargetConfig` used for forward declaration. -/
declare_opaque_type OpaqueTargetConfig
