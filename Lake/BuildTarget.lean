/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Target
import Lake.BuildMonad

open System
namespace Lake

--------------------------------------------------------------------------------
-- # Build Targets
--------------------------------------------------------------------------------

/-- A Lake build target. -/
abbrev BuildTarget i := Target i BuildM BuildTask BuildTrace

-- ## Active

/-- An active Lake build target. -/
abbrev ActiveBuildTarget i := ActiveTarget i BuildTask BuildTrace

--------------------------------------------------------------------------------
-- # File Targets
--------------------------------------------------------------------------------

/-- A `BuildTarget` that produces a file. -/
abbrev FileTarget := BuildTarget FilePath
instance : Coe FilePath FileTarget := ⟨Target.computeAsync⟩

-- ## Active

/-- An `ActiveBuildTarget` that produces a file. -/
abbrev ActiveFileTarget := ActiveBuildTarget FilePath

--------------------------------------------------------------------------------
-- # Opaque Targets
--------------------------------------------------------------------------------

/-- A `BuildTarget` with no artifact information. -/
abbrev OpaqueTarget := BuildTarget PUnit

-- ## Active

/-- An `ActiveBuildTarget` with no artifact information. -/
abbrev ActiveOpaqueTarget := ActiveBuildTarget PUnit
