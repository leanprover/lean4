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
def convertLeapSecond (tz: TZif.LeapSecond) : LeapSecond :=
  { transitionTime := Internal.UnitVal.mk tz.transitionTime, correction := Internal.UnitVal.mk tz.correction }

/--
Converts a `TZif.TZifV1` structure to a `ZoneRules` structure.
-/
def convertTZifV1 (tz: TZif.TZifV1) : Option ZoneRules := do
  let mut times : Array LocalTimeType := #[]

  for i in [0:tz.header.timecnt.toNat] do
    let localType := tz.localTimeTypes.get! i
    let abbreviation := tz.abbreviations.get! i
    let wallflag := convertWall <| tz.stdWallIndicators.get! i
    let utLocal := convertUt <| tz.utLocalIndicators.get! i
    times := times.push {
      gmtOffset := Internal.UnitVal.mk localType.gmtOffset
      isDst := localType.isDst
      abbreviation
      wall := wallflag
      utLocal
    }

  let mut transitions := #[]
  let leapSeconds := tz.leapSeconds.map convertLeapSecond

  for i in [0:tz.transitionTimes.size] do
    let time := tz.transitionTimes.get! i
    let time := Internal.UnitVal.mk time
    let indice ← tz.transitionIndices.get? i
    transitions := transitions.push { time, localTimeType := times.get! indice.toNat }

  some { leapSeconds,transitions }

/--
Converts a `TZif.TZifV2` structure to a `ZoneRules` structure.
-/
def convertTZifV2 (tz: TZif.TZifV2) : Option ZoneRules := do
   convertTZifV1 tz.toTZifV1

/--
Converts a `TZif.TZif` structure to a `ZoneRules` structure.
-/
def convertTZif (tz: TZif.TZif) : Option ZoneRules := do
  if let some v2 := tz.v2 then
    convertTZifV2 v2
  else
    convertTZifV1 tz.v1
