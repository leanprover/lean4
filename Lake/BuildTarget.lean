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
abbrev BuildTarget a :=
  Target LakeTrace BuildM BuildTask a

namespace BuildTarget

abbrev hash (self : BuildTarget a) := self.trace.hash
abbrev mtime (self : BuildTarget a) := self.trace.mtime

end BuildTarget

-- ## Active

/-- An active Lake build target. -/
abbrev ActiveBuildTarget a :=
  ActiveTarget LakeTrace BuildTask a

namespace ActiveBuildTarget

abbrev hash (self : ActiveBuildTarget a) := self.trace.hash
abbrev mtime (self : ActiveBuildTarget a) := self.trace.mtime

end ActiveBuildTarget

--------------------------------------------------------------------------------
-- # File Targets
--------------------------------------------------------------------------------

/-- A `BuildTarget` that produces a file. -/
abbrev FileTarget :=
  BuildTarget FilePath

namespace FileTarget

abbrev compute (file : FilePath) : IO FileTarget :=
  Target.compute file

end FileTarget

-- ## Active

/-- An `ActiveBuildTarget` that produces a file. -/
abbrev ActiveFileTarget :=
  ActiveBuildTarget FilePath

--------------------------------------------------------------------------------
-- # Opaque Targets
--------------------------------------------------------------------------------

/-- A `BuildTarget` with no artifact information. -/
abbrev OpaqueTarget :=
  BuildTarget PUnit

namespace OpaqueTarget

abbrev nil : OpaqueTarget :=
  Target.pure () LakeTrace.nil

abbrev collectList (targets : List (BuildTarget a)) : OpaqueTarget :=
  Target.collectOpaqueList targets

abbrev collectArray (targets : Array (BuildTarget a)) : OpaqueTarget :=
  Target.collectOpaqueArray targets

def andThenTargetAsync (t1 t2 : OpaqueTarget) : OpaqueTarget :=
  let trace := mixTrace t1.trace t2.trace
  Target.opaque trace do
    let tk1 ← t1.materializeAsync
    let tk2 ← t2.materializeAsync
    andThenAsync tk1 tk2

end OpaqueTarget

-- ## Active

/-- An `ActiveBuildTarget` with no artifact information. -/
abbrev ActiveOpaqueTarget :=
  ActiveBuildTarget PUnit

namespace ActiveOpaqueTarget

abbrev nil : ActiveOpaqueTarget :=
  ActiveTarget.pure () LakeTrace.nil

abbrev collectList (targets : List (ActiveBuildTarget a)) : BuildM ActiveOpaqueTarget :=
  ActiveTarget.collectOpaqueList targets

abbrev collectArray (targets : Array (ActiveBuildTarget a)) : BuildM ActiveOpaqueTarget :=
  ActiveTarget.collectOpaqueArray targets

def andThenTargetAsync (t1 t2 : ActiveOpaqueTarget) : BuildM ActiveOpaqueTarget := do
  let trace := mixTrace t1.trace t2.trace
  ActiveTarget.opaque trace <| ← andThenAsync t1.task t2.task

end ActiveOpaqueTarget
