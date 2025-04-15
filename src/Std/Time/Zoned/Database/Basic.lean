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
A timezone database from which we can read the `ZoneRules` of some area by it's id.
-/
protected class Database (α : Type) where

  /--
  Retrieves the zone rules information (`ZoneRules`) for a given area at a specific point in time.
  -/
  getZoneRules : α → String → IO TimeZone.ZoneRules

  /--
  Retrieves the local zone rules information (`ZoneRules`) at a given timestamp.
  -/
  getLocalZoneRules : α → IO TimeZone.ZoneRules

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
Converts a given time index into a `LocalTimeType` by using a time zone (`tz`) and its identifier.
-/
def convertLocalTimeType (index : Nat) (tz : TZif.TZifV1) (identifier : String) : Option LocalTimeType := do
  let localType ← tz.localTimeTypes[index]?
  let offset := Offset.ofSeconds <| .ofInt localType.gmtOffset
  let abbreviation ← tz.abbreviations.getD index (offset.toIsoString true)
  let wallflag := convertWall (tz.stdWallIndicators.getD index true)
  let utLocal := convertUt (tz.utLocalIndicators.getD index true)

  return {
    gmtOffset := offset
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
  let time := tz.transitionTimes[index]!
  let time := Second.Offset.ofInt time
  let indice := tz.transitionIndices[index]!
  return { time, localTimeType := times[indice.toNat]! }

/--
Converts a `TZif.TZifV1` structure to a `ZoneRules` structure.
-/
def convertTZifV1 (tz : TZif.TZifV1) (id : String) : Except String ZoneRules := do
  let mut times : Array LocalTimeType := #[]

  for i in [0:tz.header.typecnt.toNat] do
    if let some result := convertLocalTimeType i tz id
      then times := times.push result
      else .error s!"cannot convert local time {i} of the file"

  let mut transitions := #[]

  for i in [0:tz.transitionTimes.size] do
    if let some result := convertTransition times i tz
      then transitions := transitions.push result
      else .error s!"cannot convert transition {i} of the file"

  -- Local time for timestamps before the first transition is specified by the first time
  -- type (time type 0).

  let initialLocalTimeType ←
    if let some res := convertLocalTimeType 0 tz id
      then .ok res
      else .error s!"empty transitions for {id}"

  .ok { transitions, initialLocalTimeType }

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
