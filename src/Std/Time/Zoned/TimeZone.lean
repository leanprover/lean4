/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Time
public import Std.Time.DateTime.Timestamp

public section

namespace Std
namespace Time

set_option linter.all true

namespace TimeZone

/--
Represents a timezone offset as a total number of seconds from UTC.
-/
@[ext]
structure Offset where

  /--
  Creates an `Offset` from a given number of seconds.
  -/
  ofSeconds ::

  /--
  The same timezone offset in seconds.
  -/
  second : Second.Offset
deriving Repr, DecidableEq

instance : Inhabited Offset where
  default := ⟨0⟩

instance : Ord Offset where
  compare := compareOn (·.second)

theorem Offset.compare_def :
    compare (α := Offset) = compareOn (·.second) := rfl

instance : TransOrd Offset := inferInstanceAs <| TransCmp (compareOn _)

instance : LawfulEqOrd Offset where
  eq_of_compare {a b} h := by
    simp only [Offset.compare_def] at h
    apply Offset.ext
    exact LawfulEqOrd.eq_of_compare h

namespace Offset

/--
Converts an `Offset` to a string in ISO 8601 format. The `colon` parameter determines if the hour
and minute components are separated by a colon (e.g., "+01:00" or "+0100").
-/
def toIsoString (offset : Offset) (colon : Bool) : String :=
  let (sign, time) := if offset.second.val ≥ 0 then ("+", offset.second) else ("-", -offset.second)
  let hour : Hour.Offset := time.toHours
  let minute := Int.ediv (Int.tmod time.val 3600) 60
  let hourStr := if hour.val < 10 then s!"0{hour.val}" else toString hour.val
  let minuteStr := if minute < 10 then s!"0{minute}" else toString minute
    if colon then s!"{sign}{hourStr}:{minuteStr}"
    else s!"{sign}{hourStr}{minuteStr}"

/--
A zero `Offset` representing UTC (no offset).
-/
def zero : Offset :=
  { second := 0 }

/--
Creates an `Offset` from a given number of hour.
-/
def ofHours (n : Hour.Offset) : Offset :=
  ofSeconds n.toSeconds

/--
Creates an `Offset` from a given number of hours and minutes.
-/
def ofHoursAndMinutes (n : Hour.Offset) (m : Minute.Offset) : Offset :=
  ofSeconds (n.toSeconds + m.toSeconds)

end TimeZone.Offset

/--
A TimeZone structure that stores the timezone offset, the name, abbreviation and if it's in daylight
saving time.
-/
structure TimeZone where

  /--
  The `Offset` of the date time.
  -/
  offset : TimeZone.Offset

  /--
  The name of the time zone.
  -/
  name : String

  /--
  The abbreviation of the time zone.
  -/
  abbreviation : String

  /--
  Day light saving flag.
  -/
  isDST : Bool
deriving Inhabited, Repr, DecidableEq

namespace TimeZone

/--
A zeroed `Timezone` representing UTC (no offset).
-/
def UTC : TimeZone :=
  TimeZone.mk (Offset.zero) "UTC" "UTC" false

/--
A zeroed `Timezone` representing GMT (no offset).
-/
def GMT : TimeZone :=
  TimeZone.mk (Offset.zero) "Greenwich Mean Time" "GMT" false

/--
Creates a `Timestamp` from a given number of hour.
-/
def ofHours (name : String) (abbreviation : String) (n : Hour.Offset) (isDST : Bool := false) : TimeZone :=
  TimeZone.mk (Offset.ofHours n) name abbreviation isDST

/--
Creates a `Timestamp` from a given number of second.
-/
def ofSeconds (name : String) (abbreviation : String) (n : Second.Offset) (isDST : Bool := false) : TimeZone :=
  TimeZone.mk (Offset.ofSeconds n) name abbreviation isDST

/--
Gets the number of seconds in a timezone offset.
-/
def toSeconds (tz : TimeZone) : Second.Offset :=
  tz.offset.second

end TimeZone

namespace Timestamp

/--
Converts a `Timestamp` to a `WallTime` for a given timezone `offset`. The result is the local
civil time: `wall = UTC + offset`.
-/
@[inline]
def toWallTime (ts : Timestamp) (offset : TimeZone.Offset) : WallTime :=
  WallTime.ofDuration (ts.val + offset.second)

/--
Creates a `Timestamp` from a `WallTime` and a timezone `offset`. Assumes the `WallTime` represents
civil time at the given offset: `UTC = wall − offset`.
-/
@[inline]
def ofWallTime (wt : WallTime) (offset : TimeZone.Offset) : Timestamp :=
  Timestamp.ofDurationSinceUnixEpoch (wt.val - offset.second)

end Timestamp

namespace WallTime

/--
Converts a `WallTime` to a `Timestamp` given a timezone `offset`. The `WallTime` is treated as
civil time at the given offset: `UTC = wall − offset`.
-/
@[inline]
def toTimestamp (wt : WallTime) (offset : TimeZone.Offset) : Timestamp :=
  Timestamp.ofWallTime wt offset

/--
Creates a `WallTime` from a `Timestamp` given a timezone `offset`. The result is the local
civil time: `wall = UTC + offset`.
-/
@[inline]
def ofTimestamp (ts : Timestamp) (offset : TimeZone.Offset) : WallTime :=
  Timestamp.toWallTime ts offset

end WallTime
