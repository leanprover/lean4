/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Config.ConfigTarget

namespace Lake
open Lean System

/-- An input file -- its package plus its configuration. -/
abbrev InputFile := ConfigTarget InputFile.configKind

/-- An input directory -- its package plus its configuration. -/
abbrev InputDir := ConfigTarget InputDir.configKind
