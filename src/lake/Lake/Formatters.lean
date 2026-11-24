/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Huisinga
-/
module

prelude
public import Lake.Formatters.Build
public import Lake.Formatters.Config
public import Lake.Formatters.DSL
public import Lake.Formatters.Util

/-! # `Lake.Formatters`

This module imports (and thus registers) the auto-formatters for the syntax that Lake declares.
The formatters mirror the module structure of the syntax they format,
e.g. the formatters for the syntax of `Lake.Config.Meta` live in `Lake.Formatters.Config.Meta`.
-/
