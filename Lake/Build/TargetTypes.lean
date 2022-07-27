/-
Copyright (c) 2021 Mac Malone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mac Malone
-/
import Lake.Build.Job
import Lake.Build.Target

namespace Lake

--------------------------------------------------------------------------------
/-! # Build Targets -/
--------------------------------------------------------------------------------

/-- A Lake build target. -/
abbrev BuildTarget i := Target i SchedulerM Job BuildTrace

namespace BuildTarget

abbrev activate (self : BuildTarget i) : SchedulerM (BuildJob i) :=
  Target.activate self

abbrev bindSync (self : BuildTarget i) (f : i → BuildTrace → BuildM β) :=
  Target.bindSync self f

abbrev bindOpaqueSync (self : BuildTarget i) (f : BuildTrace → BuildM β) :=
  Target.bindOpaqueSync self f

end BuildTarget

--------------------------------------------------------------------------------
/-! # Common Targets -/
--------------------------------------------------------------------------------

export System (FilePath)

/-- A `BuildTarget` that produces a file. -/
abbrev FileTarget := BuildTarget FilePath

/--
A dynamic/shared library for linking.
Represented by an optional `-L` library directory × a `-l` library name.
-/
abbrev Dynlib := Option FilePath × String

/-- A `BuildTarget` that produces a `Dynlib`. -/
abbrev DynlibTarget := BuildTarget Dynlib

/-- A `BuildTarget` with no artifact information. -/
abbrev OpaqueTarget := BuildTarget Unit
