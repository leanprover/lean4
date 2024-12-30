/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Job
import Lake.Build.Data

namespace Lake
open Lean System

/-- A external library's declarative configuration. -/
structure ExternLibConfig (pkgName name : Name) where
  /-- The library's build data. -/
  getJob : CustomData (pkgName, .str name "static") → BuildJob FilePath
  deriving Inhabited

/-- A dependently typed configuration based on its registered package and name. -/
structure ExternLibDecl where
  pkg : Name
  name : Name
  config : ExternLibConfig pkg name
