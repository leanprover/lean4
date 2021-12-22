/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Target
import Lake.Build.Context

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

-- ## Active

/-- An `ActiveBuildTarget` that produces a file. -/
abbrev ActiveFileTarget := ActiveBuildTarget FilePath

--------------------------------------------------------------------------------
-- # Opaque Targets
--------------------------------------------------------------------------------

/-- A `BuildTarget` with no artifact information. -/
abbrev OpaqueTarget := BuildTarget PUnit

@[inline] def OpaqueTarget.mk (act : BuildM (BuildTask BuildTrace)) : OpaqueTarget :=
  Target.opaque act

@[inline] def OpaqueTarget.async (act : BuildM BuildTrace) : OpaqueTarget :=
  Target.opaqueAsync act

-- ## Active

/-- An `ActiveBuildTarget` with no artifact information. -/
abbrev ActiveOpaqueTarget := ActiveBuildTarget PUnit
