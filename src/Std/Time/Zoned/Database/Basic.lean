/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
import Std.Time.Zoned.Database.TzIf
import Std.Time.Zoned.ZoneRules
import Std.Time.Zoned.TimeZone
import Std.Time.DateTime

namespace Std
namespace Time
namespace TimeZone
namespace Database

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
def convetLocalTime (index : Nat) (tz : TZif.TZifV1) : Option LocalTimeType := do
  let localType ← tz.localTimeTypes.get? index
  let abbreviation ← tz.abbreviations.get? index
  let wallflag ← convertWall <$> tz.stdWallIndicators.get? index
  let utLocal ← convertUt <$> tz.utLocalIndicators.get? index

  return {
    gmtOffset := Offset.ofSeconds <| Internal.UnitVal.mk localType.gmtOffset
    isDst := localType.isDst
    abbreviation
    wall := wallflag
    utLocal
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
def convertTZifV1 (tz : TZif.TZifV1) : Except String ZoneRules := do
  let mut times : Array LocalTimeType := #[]

  for i in [0:tz.header.typecnt.toNat] do
    if let some result := convetLocalTime i tz
      then times := times.push result
      else .error s!"cannot convert local time {i} of the file"

  let mut transitions := #[]
  let leapSeconds := tz.leapSeconds.map convertLeapSecond

  for i in [0:tz.transitionTimes.size] do
    if let some result := convertTransition times i tz
      then transitions := transitions.push result
      else .error s!"cannot convert transtiion {i} of the file"

  .ok { leapSeconds,transitions, localTimes := times }

/--
Converts a `TZif.TZifV2` structure to a `ZoneRules` structure.
-/
def convertTZifV2 (tz : TZif.TZifV2) : Except String ZoneRules := do
   convertTZifV1 tz.toTZifV1

/--
Converts a `TZif.TZif` structure to a `ZoneRules` structure.
-/
def convertTZif (tz : TZif.TZif) : Except String ZoneRules := do
  if let some v2 := tz.v2
    then convertTZifV2 v2
    else convertTZifV1 tz.v1
