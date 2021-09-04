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

namespace OpaqueTarget

abbrev nil : OpaqueTarget :=
  Target.pure () BuildTrace.nil

def mixAsync (t1 t2 : OpaqueTarget) : OpaqueTarget :=
  Target.opaque do
    let tk1 ← t1.materializeAsync
    let tk2 ← t2.materializeAsync
    bindAsync tk1 fun tr1 =>
    bindAsync tk2 fun tr2 =>
    pure <| pure <| mixTrace tr1 tr2

instance : Add OpaqueTarget := ⟨mixAsync⟩

end OpaqueTarget

-- ## Active

/-- An `ActiveBuildTarget` with no artifact information. -/
abbrev ActiveOpaqueTarget := ActiveBuildTarget PUnit

namespace ActiveOpaqueTarget

abbrev nil : ActiveOpaqueTarget :=
  ActiveTarget.pure () BuildTrace.nil

def mixAsync (t1 t2 : ActiveOpaqueTarget) : BuildM ActiveOpaqueTarget := do
  ActiveTarget.opaque <| ←
    t1.bindOpaqueAsync fun tr1 =>
    t2.bindOpaqueAsync fun tr2 =>
    pure <| pure <| mixTrace tr1 tr2

end ActiveOpaqueTarget
