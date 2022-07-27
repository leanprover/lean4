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
/-! # Build Targets -/
--------------------------------------------------------------------------------

/-- A Lake build target. -/
abbrev BuildTarget i := Target i SchedulerM BuildTask BuildTrace

/-- An active Lake build target. -/
abbrev ActiveBuildTarget i := ActiveTarget i BuildTask BuildTrace

namespace BuildTarget

abbrev activate (self : BuildTarget i) : SchedulerM (ActiveBuildTarget i) :=
  Target.activate self

abbrev bindSync (self : BuildTarget i) (f : i → BuildTrace → BuildM β) :=
  Target.bindSync self f

abbrev bindOpaqueSync (self : BuildTarget i) (f : BuildTrace → BuildM β) :=
  Target.bindOpaqueSync self f

end BuildTarget

namespace ActiveBuildTarget

abbrev bindSync (self : ActiveBuildTarget i) (f : i → BuildTrace → BuildM β) :=
  ActiveTarget.bindSync self f

abbrev bindOpaqueSync (self : ActiveBuildTarget i) (f : BuildTrace → BuildM β) :=
  ActiveTarget.bindOpaqueSync self f

end ActiveBuildTarget

--------------------------------------------------------------------------------
/-! # File Targets -/
--------------------------------------------------------------------------------

/-- A `BuildTarget` that produces a file. -/
abbrev FileTarget := BuildTarget FilePath

/--
A `BuildTarget` that produces a dynamic/shared library for lining.
Represented by an optional `-L` library directory × a `-l` library name.
-/
abbrev DynlibTarget := BuildTarget (Option FilePath × String)

/-- An `ActiveBuildTarget` that produces a file. -/
abbrev ActiveFileTarget := ActiveBuildTarget FilePath

/--
A `ActiveBuildTarget` that produces a dynamic/shared library for lining.
Represented by an optional `-L` library directory × a `-l` library name.
-/
abbrev ActiveDynlibTarget := ActiveBuildTarget (Option FilePath × String)

--------------------------------------------------------------------------------
/-! # Opaque Targets -/
--------------------------------------------------------------------------------

/-- A `BuildTarget` with no artifact information. -/
abbrev OpaqueTarget := BuildTarget Unit

/-- An `ActiveBuildTarget` with no artifact information. -/
abbrev ActiveOpaqueTarget := ActiveBuildTarget Unit
