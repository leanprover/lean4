/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.Database.TzIf

namespace Std
namespace Time

set_option linter.all true

/--
A timezone database that we can read the `ZoneRules` of some area by it's id.
-/
class Database (α : Type) where

  /--
  Loads a `ZoneRules` by it's id.
  -/
  load : α → String → IO TimeZone.ZoneRules

  /--
  Loads a `ZoneRules` that is setted by the local computer.
  -/
  localRules : α → IO TimeZone.ZoneRules

namespace TimeZone

/--
Converts a Boolean value to a corresponding `StdWall` type.
-/
def convertWall : Bool → StdWall
  | true => .standard
  | false => .wall

/--
Converts a Boolean value to a corresponding `UTLocal` type.
-/
def convertUt : Bool → UTLocal
  | true => .ut
  | false => .local

/--
Converts a `TZif.LeapSecond` structure to a `LeapSecond` structure.
-/
def convertLeapSecond (tz : TZif.LeapSecond) : LeapSecond :=
  { transitionTime := Internal.UnitVal.mk tz.transitionTime, correction := Internal.UnitVal.mk tz.correction }

/--
Converts a LocalTime.
-/
def convertLocalTime (index : Nat) (tz : TZif.TZifV1) (identifier : String) : Option LocalTimeType := do
  let localType ← tz.localTimeTypes.get? index
  let abbreviation ← tz.abbreviations.getD index "Unknown"
  let wallflag := convertWall (tz.stdWallIndicators.getD index true)
  let utLocal := convertUt (tz.utLocalIndicators.getD index true)

  return {
    gmtOffset := Offset.ofSeconds <| Internal.UnitVal.mk localType.gmtOffset
    isDst := localType.isDst
    abbreviation
    wall := wallflag
    utLocal
    identifier
  }

/--
Converts a transition.
-/
def convertTransition (times: Array LocalTimeType) (index : Nat) (tz : TZif.TZifV1) : Option Transition := do
  let time := tz.transitionTimes.get! index
  let time := Internal.UnitVal.mk time
  let indice := tz.transitionIndices.get! index
  return { time, localTimeType := times.get! indice.toNat }

/--
Converts a `TZif.TZifV1` structure to a `ZoneRules` structure.
-/
def convertTZifV1 (tz : TZif.TZifV1) (id : String) : Except String ZoneRules := do
  let mut times : Array LocalTimeType := #[]

  for i in [0:tz.header.typecnt.toNat] do
    if let some result := convertLocalTime i tz id
      then times := times.push result
      else .error s!"cannot convert local time {i} of the file"

  let mut transitions := #[]
  let leapSeconds := tz.leapSeconds.map convertLeapSecond

  for i in [0:tz.transitionTimes.size] do
    if let some result := convertTransition times i tz
      then transitions := transitions.push result
      else .error s!"cannot convert transtiion {i} of the file"

  .ok { leapSeconds, transitions, localTimes := times }

/--
Converts a `TZif.TZifV2` structure to a `ZoneRules` structure.
-/
def convertTZifV2 (tz : TZif.TZifV2) (id : String) : Except String ZoneRules := do
   convertTZifV1 tz.toTZifV1 id

/--
Converts a `TZif.TZif` structure to a `ZoneRules` structure.
-/
def convertTZif (tz : TZif.TZif) (id : String) : Except String ZoneRules := do
  if let some v2 := tz.v2
    then convertTZifV2 v2 id
    else convertTZifV1 tz.v1 id
