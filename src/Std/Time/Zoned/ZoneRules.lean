/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Zoned.TimeZone
public import Std.Time.DateTime.Timestamp
public import Std.Time.DateTime.WallTime
public import Std.Time.Zoned.RecurringRule

public section

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

  /--
  Recurring rule from the TZif footer, used to extrapolate transitions beyond the last stored entry.
  -/
  transitionRule : Option RecurringRule := none
deriving Repr, Inhabited

namespace Transition

/--
Returns the transition time as a `Timestamp`.
-/
def timestamp (t : Transition) : Timestamp :=
  Timestamp.ofSecondsSinceUnixEpoch t.time

/--
Create a TimeZone from a Transition.
-/
def createTimeZoneFromTransition (transition : Transition) : TimeZone :=
  let name := transition.localTimeType.identifier
  let offset := transition.localTimeType.gmtOffset
  let abbreviation := transition.localTimeType.abbreviation
  TimeZone.mk offset name abbreviation transition.localTimeType.isDst

/--
Finds the index of the transition in effect at a given timestamp in `Array Transition`.
Returns the index of the most recent transition that started at or before the timestamp,
or `none` if the timestamp precedes all transitions.
-/
def findTransitionIndexForTimestamp (transitions : Array Transition) (timestamp : Timestamp) : Option Nat :=
  let value := timestamp.toSecondsSinceUnixEpoch
  match transitions.findIdx? (fun t => t.time.val > value.val) with
  | some 0 => none
  | some i => some (i - 1)
  | none => if transitions.isEmpty then none else some (transitions.size - 1)

/--
Finds the transition in effect at a given timestamp in `Array Transition`.
Returns the most recent transition that started at or before the timestamp,
or `none` if the timestamp precedes all transitions.
-/
def findTransitionForTimestamp (transitions : Array Transition) (timestamp : Timestamp) : Option Transition :=
  if let some idx := findTransitionIndexForTimestamp transitions timestamp
    then transitions[idx]?
    else none

/--
Find the current `TimeZone` out of a `Transition` in a `Array Transition`
-/
def timezoneAt (transitions : Array Transition) (tm : Timestamp) : Except String TimeZone :=
  if let some transition := findTransitionForTimestamp transitions tm
    then .ok transition.createTimeZoneFromTransition
    else .error "cannot find local timezone."

end Transition
namespace RecurringRule

-- `wallOffset` is the offset in effect at the wall-clock moment of this transition:
-- DST-start times are given in standard time; DST-end times are given in DST time.
private def transitionUtcSeconds (rule : TransitionRule) (year : Year.Offset) (wallOffset : Offset) : Second.Offset :=
  (TransitionSpec.toEpochDay rule.spec year).toSeconds + rule.time - wallOffset.second

/--
Returns the `TimeZone` in effect for this `RecurringRule` at the given `Timestamp`.

If no DST rule is defined, or if either transition rule is missing, the standard zone is returned
unconditionally. Otherwise the function computes the UTC timestamps at which DST starts and ends
for the year containing `tm`, and returns the DST zone when the timestamp falls inside the DST
interval (accounting for rules that wrap across a year boundary in the Southern Hemisphere).
-/
def timezoneAt (rule : RecurringRule) (tm : Timestamp) : TimeZone := Id.run do
  let stdTz := TimeZone.mk rule.stdOffset rule.stdName rule.stdName false
  let some dst := rule.dst | return stdTz
  let dstTz := TimeZone.mk dst.offset dst.name dst.name true

  let some startRule := dst.start | return stdTz
  let some endRule   := dst.end_  | return stdTz

  let secs := tm.toSecondsSinceUnixEpoch

  let year  := PlainDate.ofEpochDay (Day.Offset.ofSeconds secs) |>.year

  -- DST-start wall clock is standard time; DST-end wall clock is DST time (POSIX §8.3).
  let dstStart := transitionUtcSeconds startRule year rule.stdOffset
  let dstEnd   := transitionUtcSeconds endRule year dst.offset

  if dstStart ≤ dstEnd then
    if dstStart ≤ secs && secs < dstEnd then dstTz else stdTz
  else
    -- Southern Hemisphere: DST spans the year boundary
    if secs < dstEnd || dstStart ≤ secs then dstTz else stdTz

end RecurringRule

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
  fixedOffsetZone 0 (some "UTC") (some "UTC")

/--
Finds the `LocalTimeType` corresponding to a given `Timestamp` in `ZoneRules`.
If the timestamp falls between two transitions, it returns the most recent transition before the timestamp.
When the timestamp is beyond all stored transitions and a POSIX TZ footer rule is present, the rule is
consulted. Falls back to `initialLocalTimeType` if no transition or rule applies.
-/
def findLocalTimeTypeForTimestamp (zr : ZoneRules) (timestamp : Timestamp) : LocalTimeType := Id.run do
  let some lastIdx := Transition.findTransitionIndexForTimestamp zr.transitions timestamp
    | return zr.initialLocalTimeType

  let some t := zr.transitions[lastIdx]?
    | return zr.initialLocalTimeType

  let some rule := if lastIdx + 1 == zr.transitions.size then zr.transitionRule else none
    | return t.localTimeType

  let tz := rule.timezoneAt timestamp

  return { t.localTimeType with gmtOffset := tz.offset, isDst := tz.isDST, abbreviation := tz.abbreviation, identifier := tz.name }

/--
Finds the `LocalTimeType` for a given wall-clock time (seconds since 1970-01-01T00:00:00 in local time).
Unlike `findLocalTimeTypeForTimestamp`, this compares each transition's UTC time adjusted by the
previous offset — necessary when converting local time to UTC.

When the wall time falls beyond all stored transitions and a `transitionRule` is present, the
recurring rule is used to determine the timezone (converting the wall time to UTC via the last
known offset before consulting the rule).
-/
def findLocalTimeTypeForWallTime (zr : ZoneRules) (wallTime : WallTime) : LocalTimeType := Id.run do
  let mut ltt := zr.initialLocalTimeType

  for t in zr.transitions do
    let localTransitionTime := t.timestamp.toWallTime ltt.gmtOffset
    if wallTime < localTransitionTime then
      return ltt
    ltt := t.localTimeType

  if let some rule := zr.transitionRule then
    -- Convert wall time to an approximate UTC timestamp using the last known offset.
    let approxUtc : Timestamp := wallTime.toTimestamp ltt.gmtOffset
    let tz := rule.timezoneAt approxUtc
    return { ltt with gmtOffset := tz.offset, isDst := tz.isDST, abbreviation := tz.abbreviation, identifier := tz.name }

  return ltt

/--
Find the current `TimeZone` out of a `Transition` in a `ZoneRules`
-/
def timezoneAt (zr : ZoneRules) (tm : Timestamp) : TimeZone :=
  (zr.findLocalTimeTypeForTimestamp tm).getTimeZone

/--
Creates `ZoneRules` for the given `TimeZone`.
-/
@[inline]
def ofTimeZone (tz : TimeZone) : ZoneRules :=
  let ltt :=  LocalTimeType.mk tz.offset tz.isDST tz.abbreviation .wall .local tz.name
  ZoneRules.mk ltt #[] none

end ZoneRules
