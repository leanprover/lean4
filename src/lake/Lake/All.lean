/-
Copyright (c) 2026 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
module

prelude
public import Lake
public import Lake.Build
public import Lake.CLI
public import Lake.Config
public import Lake.DSL
public import Lake.Load
public import Lake.Reservoir
public import Lake.Toml
public import Lake.Util
public import Lake.Version

/-! # `Lake.All`

This module imports (and thus initializes) every Lake module. Its existence is important for the
Lean core build. Users of the Lake DSL are expected to import `Lake` instead in configuration files.
It imports a smaller set of modules better targeted to that use (excluding things like the CLI).
-/
