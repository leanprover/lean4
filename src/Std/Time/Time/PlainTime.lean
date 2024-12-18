/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Time.Basic

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents a specific point in a day, including hours, minutes, seconds, and nanoseconds.
-/
structure PlainTime (leap : Bool) where

  /--
  `Hour` component of the `PlainTime`
  -/
  hour : Hour.Ordinal

  /--
  `Minute` component of the `PlainTime`
  -/
  minute : Minute.Ordinal

  /--
  `Second` component of the `PlainTime`
  -/
  second : Second.Ordinal leap

  /--
  `Nanoseconds` component of the `PlainTime`
  -/
  nanosecond : Nanosecond.Ordinal
  deriving Repr

/--
COMMENT
-/
def LeapTime := PlainTime True

instance : Inhabited (PlainTime x) where
  default := ⟨0, 0, 0, 0, by decide⟩

instance : BEq (PlainTime x) where
  beq x y := x.hour.val == y.hour.val && x.minute == y.minute
          && x.second.val == y.second.val && x.nanosecond == y.nanosecond

namespace PlainTime

/--
Creates a `PlainTime` value representing midnight (00:00:00.000000000).
-/
def midnight : PlainTime α :=
  ⟨0, 0, 0, 0⟩

/--
Creates a `PlainTime` value from the provided hours, minutes, seconds and nanoseconds components.
-/
@[inline]
def ofHourMinuteSecondsNano (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal α) (nano : Nanosecond.Ordinal) : PlainTime α :=
  ⟨hour, minute, second, nano⟩

/--
Creates a `PlainTime` value from the provided hours, minutes, and seconds.
-/
@[inline]
def ofHourMinuteSeconds (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal α) : PlainTime α :=
  ofHourMinuteSecondsNano hour minute second 0

/--
Converts a `PlainTime` value to the total number of milliseconds.
-/
def toMilliseconds (time : PlainTime α) : Millisecond.Offset :=
  time.hour.toOffset.toMilliseconds +
  time.minute.toOffset.toMilliseconds +
  time.second.toOffset.toMilliseconds +
  time.nanosecond.toOffset.toMilliseconds

/--
Converts a `PlainTime` value to the total number of nanoseconds.
-/
def toNanoseconds (time : PlainTime α) : Nanosecond.Offset :=
  time.hour.toOffset.toNanoseconds +
  time.minute.toOffset.toNanoseconds +
  time.second.toOffset.toNanoseconds +
  time.nanosecond.toOffset

/--
Converts a `PlainTime` value to the total number of seconds.
-/
def toSeconds (time : PlainTime α) : Second.Offset :=
  time.hour.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.toOffset

/--
Converts a `PlainTime` value to the total number of minutes.
-/
def toMinutes (time : PlainTime α) : Minute.Offset :=
  time.hour.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.toOffset.toMinutes

/--
Converts a `PlainTime` value to the total number of hours.
-/
def toHours (time : PlainTime α) : Hour.Offset :=
  time.hour.toOffset

/--
Creates a `PlainTime` value from a total number of nanoseconds.
-/
def ofNanoseconds (nanos : Nanosecond.Offset) : PlainTime α :=
  have totalSeconds := nanos.ediv 1000000000
  have remainingNanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  have hours := Bounded.LE.byEmod (totalSeconds.val / 3600) 24 (by decide)
  have minutes := (Bounded.LE.byEmod totalSeconds.val 3600 (by decide)).ediv 60 (by decide)

  have seconds := Bounded.LE.byEmod totalSeconds.val 60 (by decide)

  have seconds :=
    match α with
    | true => seconds.expandTop (by decide)
    | false => seconds

  let nanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  PlainTime.mk hours minutes seconds nanos

/--
Creates a `PlainTime` value from a total number of millisecond.
-/
@[inline]
def ofMilliseconds (millis : Millisecond.Offset) : PlainTime α :=
  ofNanoseconds millis.toNanoseconds

/--
Creates a `PlainTime` value from a total number of seconds.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : PlainTime α :=
  ofNanoseconds secs.toNanoseconds

/--
Creates a `PlainTime` value from a total number of minutes.
-/
@[inline]
def ofMinutes (secs : Minute.Offset) : PlainTime α :=
  ofNanoseconds secs.toNanoseconds

/--
Creates a `PlainTime` value from a total number of hours.
-/
@[inline]
def ofHours (hour : Hour.Offset) : PlainTime α :=
  ofNanoseconds hour.toNanoseconds

/--
Adds seconds to a `PlainTime`.
-/
@[inline]
def addSeconds (time : PlainTime α) (secondsToAdd : Second.Offset) : PlainTime α :=
  let totalSeconds := time.toNanoseconds + secondsToAdd.toNanoseconds
  ofNanoseconds totalSeconds

/--
Subtracts seconds from a `PlainTime`.
-/
@[inline]
def subSeconds (time : PlainTime α) (secondsToSub : Second.Offset) : PlainTime α :=
  addSeconds time (-secondsToSub)

/--
Adds minutes to a `PlainTime`.
-/
@[inline]
def addMinutes (time : PlainTime α) (minutesToAdd : Minute.Offset) : PlainTime α :=
  let total := time.toNanoseconds + minutesToAdd.toNanoseconds
  ofNanoseconds total

/--
Subtracts minutes from a `PlainTime`.
-/
@[inline]
def subMinutes (time : PlainTime α) (minutesToSub : Minute.Offset) : PlainTime α :=
  addMinutes time (-minutesToSub)

/--
Adds hours to a `PlainTime`.
-/
@[inline]
def addHours (time : PlainTime α) (hoursToAdd : Hour.Offset) : PlainTime α :=
  let total := time.toNanoseconds + hoursToAdd.toNanoseconds
  ofNanoseconds total

/--
Subtracts hours from a `PlainTime`.
-/
@[inline]
def subHours (time : PlainTime α) (hoursToSub : Hour.Offset) : PlainTime α :=
  addHours time (-hoursToSub)

/--
Adds nanoseconds to a `PlainTime`.
-/
def addNanoseconds (time : PlainTime α) (nanosToAdd : Nanosecond.Offset) : PlainTime α :=
  let total := time.toNanoseconds + nanosToAdd
  ofNanoseconds total

/--
Subtracts nanoseconds from a `PlainTime`.
-/
def subNanoseconds (time : PlainTime α) (nanosToSub : Nanosecond.Offset) : PlainTime α :=
  addNanoseconds time (-nanosToSub)

/--
Adds milliseconds to a `PlainTime`.
-/
def addMilliseconds (time : PlainTime α) (millisToAdd : Millisecond.Offset) : PlainTime α :=
  let total := time.toMilliseconds + millisToAdd
  ofMilliseconds total

/--
Subtracts milliseconds from a `PlainTime`.
-/
def subMilliseconds (time : PlainTime α) (millisToSub : Millisecond.Offset) : PlainTime α :=
  addMilliseconds time (-millisToSub)

/--
Creates a new `PlainTime` by adjusting the `second` component to the given value.
-/
@[inline]
def withSeconds (pt : PlainTime α) (second : Second.Ordinal α) : PlainTime α :=
  { pt with second := second }

/--
Creates a new `PlainTime` by adjusting the `minute` component to the given value.
-/
@[inline]
def withMinutes (pt : PlainTime α) (minute : Minute.Ordinal) : PlainTime α :=
  { pt with minute := minute }

/--
Creates a new `PlainTime` by adjusting the milliseconds component inside the `nano` component of its `time` to the given value.
-/
@[inline]
def withMilliseconds (pt : PlainTime α) (millis : Millisecond.Ordinal) : PlainTime α :=
  let minorPart := pt.nanosecond.emod 1000 (by decide)
  let majorPart := millis.mul_pos 1000000 (by decide) |>.addBounds minorPart
  { pt with nanosecond := majorPart |>.expandTop (by decide) }

/--
Creates a new `PlainTime` by adjusting the `nano` component to the given value.
-/
@[inline]
def withNanoseconds (pt : PlainTime α) (nano : Nanosecond.Ordinal) : PlainTime α :=
  { pt with nanosecond := nano }

/--
Creates a new `PlainTime` by adjusting the `hour` component to the given value.
-/
@[inline]
def withHours (pt : PlainTime α) (hour : Hour.Ordinal) : PlainTime α :=
  { pt with hour := hour }

/--
`Millisecond` component of the `PlainTime`
-/
@[inline]
def millisecond (pt : PlainTime α) : Millisecond.Ordinal :=
  pt.nanosecond.ediv 1000000 (by decide)

instance : HAdd (PlainTime α) Nanosecond.Offset (PlainTime α) where
  hAdd := addNanoseconds

instance : HSub (PlainTime α) Nanosecond.Offset (PlainTime α) where
  hSub := subNanoseconds

instance : HAdd (PlainTime α) Millisecond.Offset (PlainTime α) where
  hAdd := addMilliseconds

instance : HSub (PlainTime α) Millisecond.Offset (PlainTime α) where
  hSub := subMilliseconds

instance : HAdd (PlainTime α) Second.Offset (PlainTime α) where
  hAdd := addSeconds

instance : HSub (PlainTime α) Second.Offset (PlainTime α) where
  hSub := subSeconds

instance : HAdd (PlainTime α) Minute.Offset (PlainTime α) where
  hAdd := addMinutes

instance : HSub (PlainTime α) Minute.Offset (PlainTime α) where
  hSub := subMinutes

instance : HAdd (PlainTime α) Hour.Offset (PlainTime α) where
  hAdd := addHours

instance : HSub (PlainTime α) Hour.Offset (PlainTime α) where
  hSub := subHours

end PlainTime
end Time
end Std
