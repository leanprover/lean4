/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Init.Prelude
meta import all Lake.Util.OpaqueType
import Lake.Util.OpaqueType

namespace Lake

/-- Opaque reference to a `Workspace` used for forward declaration. -/
public nonempty_type OpaqueWorkspace

/-- Opaque reference to a `TargetConfig` used for forward declaration. -/
public nonempty_type OpaqueTargetConfig (pkgName name : Lean.Name)
