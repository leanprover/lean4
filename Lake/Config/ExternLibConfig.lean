/-
Copyright (c) 2022 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.TargetTypes

namespace Lake
open Lean System

/-- A external library's declarative configuration. -/
structure ExternLibConfig where
  /-- The name of the target. -/
  name : Name

  /-- The library's build target. -/
  target : FileTarget

deriving Inhabited
