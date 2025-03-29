/-
Copyright (c) 2025 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
prelude
import Lake.Build.Data

/-!
# Lake Targets

This module contains the declarative definition of a `Target`.
-/

open Std

namespace Lake

/-- A Lake target that is expected to produce an output of a specific type. -/
structure Target (α : Type) where
  key : PartialBuildKey
  deriving Repr

instance : ToString (Target α) := ⟨(·.key.toString)⟩
instance : Coe PartialBuildKey (Target α) := ⟨Target.mk⟩

/--
Shorthand for `Array (Target α)` that supports
dot notation for Lake-specific operations (e.g., `fetch`).
-/
abbrev TargetArray α := Array (Target α)
