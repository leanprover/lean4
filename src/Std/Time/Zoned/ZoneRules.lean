/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.DateTime
import Std.Time.Zoned.TimeZone

namespace Std
namespace Time
namespace TimeZone
open Internal

set_option linter.all true

/--
Represents the type of local time in relation to UTC.
-/
inductive UTLocal
  /--
  Universal Time (UT), often referred to as UTC.
  -/
  | ut

  /--
  Local time that is not necessarily UTC.
  -/
  | local
  deriving Repr, Inhabited

/--
Represents types of wall clocks or standard times.
-/
inductive StdWall
  /--
  Time based on a wall clock, which can include daylight saving adjustments.
  -/
  | wall

  /--
  Standard time without adjustments for daylight saving.
  -/
  | standard
  deriving Repr, Inhabited

/--
Represents a type of local time, including offset and daylight saving information.
-/
structure LocalTimeType where

  /--
  The offset from GMT for this local time.
  -/
  gmtOffset : TimeZone.Offset

  /--
  Indicates if daylight saving time is observed.
  -/
  isDst : Bool

  /--
  The abbreviation for this local time type (e.g., "EST", "PDT").
  -/
  abbreviation : String

  /--
  Indicates if the time is wall clock or standard time.
  -/
  wall : StdWall

  /--
  Distinguishes between universal time and local time.
  -/
  utLocal : UTLocal

  /--
  ID of the timezone
  -/
  identifier : String
  deriving Repr, Inhabited

namespace LocalTimeType

/--
Gets the `TimeZone` offset from a `LocalTimeType`.
-/
def getTimeZone (time : LocalTimeType) : TimeZone :=
  ⟨time.gmtOffset, time.identifier, time.abbreviation, time.isDst⟩

end LocalTimeType

/--
Represents a time zone transition, mapping a time to a local time type.
-/
structure Transition where

  /--
  The specific time of the transition event.
  -/
  time : Second.Offset

  /--
  The local time type associated with this transition.
  -/
  localTimeType : LocalTimeType
  deriving Repr, Inhabited

/--
Represents the rules for a time zone.
-/
structure ZoneRules where

  /--
  The first `LocalTimeType` used as a fallback when no matching transition is found.
  -/
  initialLocalTimeType : LocalTimeType

  /--
  The array of transitions for the time zone.
  -/
  transitions : Array Transition

  deriving Repr, Inhabited

namespace Transition

/--
Create a TimeZone from a Transition.
-/
def createTimeZoneFromTransition (transition : Transition) : TimeZone :=
  let name := transition.localTimeType.identifier
  let offset := transition.localTimeType.gmtOffset
  let abbreviation := transition.localTimeType.abbreviation
  TimeZone.mk offset name abbreviation transition.localTimeType.isDst

/--
Applies the transition to a Timestamp.
-/
def apply (timestamp : Timestamp) (transition : Transition) : Timestamp :=
  let offsetInSeconds := transition.localTimeType.gmtOffset.second |>.add transition.localTimeType.gmtOffset.second
  timestamp.addSeconds offsetInSeconds

/--
Finds the transition corresponding to a given timestamp in `Array Transition`.
If the timestamp falls between two transitions, it returns the most recent transition before the timestamp.
-/
def findTransitionIndexForTimestamp (transitions : Array Transition) (timestamp : Timestamp) : Option Nat :=
  let value := timestamp.toSecondsSinceUnixEpoch
  transitions.findIdx? (fun t => t.time.val > value.val)

/--
Finds the transition corresponding to a given timestamp in `Array Transition`.
If the timestamp falls between two transitions, it returns the most recent transition before the timestamp.
-/
def findTransitionForTimestamp (transitions : Array Transition) (timestamp : Timestamp) : Option Transition :=
  if let some idx := findTransitionIndexForTimestamp transitions timestamp
    then transitions[idx - 1]?
    else transitions.back?

/--
Find the current `TimeZone` out of a `Transition` in a `Array Transition`
-/
def timezoneAt (transitions : Array Transition) (tm : Timestamp) : Except String TimeZone :=
  if let some transition := findTransitionForTimestamp transitions tm
    then .ok transition.createTimeZoneFromTransition
    else .error "cannot find local timezone."

end Transition
namespace ZoneRules

/--
Creates ZoneRules with a fixed GMT offset.
-/
def fixedOffsetZone (second : Second.Offset) (identifier : Option String := none) (abbreviation : Option String := none) : ZoneRules :=
  let offset : Offset := { second }
  {
    transitions := #[],
    initialLocalTimeType := {
      gmtOffset := offset,
      isDst := false, abbreviation := abbreviation.getD (offset.toIsoString true),
      wall := .standard,
      utLocal := .ut,
      identifier := identifier.getD (offset.toIsoString true)
    }
  }

/--
Creates ZoneRules with a fixed offset of UTC (GMT+0).
-/
@[inline]
def UTC : ZoneRules :=
  fixedOffsetZone 0 "UTC" "UTC"

/--
Finds the `LocalTimeType` corresponding to a given `Timestamp` in `ZoneRules`.
If the timestamp falls between two transitions, it returns the most recent transition before the timestamp.
If no transition is found, it falls back to `initialLocalTimeType`.
-/
@[inline]
def findLocalTimeTypeForTimestamp (zr : ZoneRules) (timestamp : Timestamp) : LocalTimeType :=
  Transition.findTransitionForTimestamp zr.transitions timestamp
  |>.map (·.localTimeType)
  |>.getD zr.initialLocalTimeType

/--
Find the current `TimeZone` out of a `Transition` in a `ZoneRules`
-/
@[inline]
def timezoneAt (zr : ZoneRules) (tm : Timestamp) : TimeZone :=
  Transition.timezoneAt zr.transitions tm
  |>.toOption
  |>.getD (zr.initialLocalTimeType |>.getTimeZone)

/--
Creates `ZoneRules` for the given `TimeZone`.
-/
@[inline]
def ofTimeZone (tz : TimeZone) : ZoneRules :=
  let ltt :=  LocalTimeType.mk tz.offset tz.isDST tz.abbreviation .wall .local tz.name
  ZoneRules.mk ltt #[]

end ZoneRules
