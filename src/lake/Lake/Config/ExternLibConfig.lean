/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Job

namespace Lake
open Lean System

/-- A external library's declarative configuration. -/
structure ExternLibConfig (pkgName name : SimpleName) where
  /-- The library's build data. -/
  getJob : CustomData (pkgName, name) → BuildJob FilePath
  deriving Inhabited

/-- A dependently typed configuration based on its registered package and name. -/
structure ExternLibDecl where
  pkg : SimpleName
  name : SimpleName
  config : ExternLibConfig pkg name
