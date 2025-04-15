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
@[ext]
structure PlainTime where

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
  second : Second.Ordinal true

  /--
  `Nanoseconds` component of the `PlainTime`
  -/
  nanosecond : Nanosecond.Ordinal
deriving Repr, DecidableEq

instance : Inhabited PlainTime where
  default := ⟨0, 0, 0, 0, by decide⟩

instance : Ord PlainTime where
  compare := compareLex (compareOn (·.hour)) <| compareLex (compareOn (·.minute)) <|
      compareLex (compareOn (·.second)) (compareOn (·.nanosecond))

theorem PlainTime.compare_def :
    compare (α := PlainTime) =
      (compareLex (compareOn (·.hour)) <| compareLex (compareOn (·.minute)) <|
          compareLex (compareOn (·.second)) (compareOn (·.nanosecond))) := rfl

instance : TransOrd PlainTime := inferInstanceAs <| TransCmp (compareLex _ _)

instance : LawfulEqOrd PlainTime where
  eq_of_compare {a b} h := by
    simp only [PlainTime.compare_def, compareLex_eq_eq] at h
    ext
    · exact LawfulEqOrd.eq_of_compare h.1
    · exact LawfulEqOrd.eq_of_compare h.2.1
    · exact LawfulEqOrd.eq_of_compare h.2.2.1
    · exact LawfulEqOrd.eq_of_compare h.2.2.2

namespace PlainTime

/--
Creates a `PlainTime` value representing midnight (00:00:00.000000000).
-/
def midnight : PlainTime :=
  ⟨0, 0, 0, 0⟩

/--
Creates a `PlainTime` value from the provided hours, minutes, seconds and nanoseconds components.
-/
@[inline]
def ofHourMinuteSecondsNano (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal true) (nano : Nanosecond.Ordinal) : PlainTime :=
  ⟨hour, minute, second, nano⟩

/--
Creates a `PlainTime` value from the provided hours, minutes, and seconds.
-/
@[inline]
def ofHourMinuteSeconds (hour : Hour.Ordinal) (minute : Minute.Ordinal) (second : Second.Ordinal true) : PlainTime :=
  ofHourMinuteSecondsNano hour minute second 0

/--
Converts a `PlainTime` value to the total number of milliseconds.
-/
def toMilliseconds (time : PlainTime) : Millisecond.Offset :=
  time.hour.toOffset.toMilliseconds +
  time.minute.toOffset.toMilliseconds +
  time.second.toOffset.toMilliseconds +
  time.nanosecond.toOffset.toMilliseconds

/--
Converts a `PlainTime` value to the total number of nanoseconds.
-/
def toNanoseconds (time : PlainTime) : Nanosecond.Offset :=
  time.hour.toOffset.toNanoseconds +
  time.minute.toOffset.toNanoseconds +
  time.second.toOffset.toNanoseconds +
  time.nanosecond.toOffset

/--
Converts a `PlainTime` value to the total number of seconds.
-/
def toSeconds (time : PlainTime) : Second.Offset :=
  time.hour.toOffset.toSeconds +
  time.minute.toOffset.toSeconds +
  time.second.toOffset

/--
Converts a `PlainTime` value to the total number of minutes.
-/
def toMinutes (time : PlainTime) : Minute.Offset :=
  time.hour.toOffset.toMinutes +
  time.minute.toOffset +
  time.second.toOffset.toMinutes

/--
Converts a `PlainTime` value to the total number of hours.
-/
def toHours (time : PlainTime) : Hour.Offset :=
  time.hour.toOffset

/--
Creates a `PlainTime` value from a total number of nanoseconds.
-/
def ofNanoseconds (nanos : Nanosecond.Offset) : PlainTime :=
  have totalSeconds := nanos.ediv 1000000000
  have remainingNanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  have hours := Bounded.LE.byEmod (totalSeconds.val / 3600) 24 (by decide)
  have minutes := (Bounded.LE.byEmod totalSeconds.val 3600 (by decide)).ediv 60 (by decide)

  have seconds := Bounded.LE.byEmod totalSeconds.val 60 (by decide)
  have seconds := seconds.expandTop (by decide)

  let nanos := Bounded.LE.byEmod nanos.val 1000000000 (by decide)
  PlainTime.mk hours minutes seconds nanos

/--
Creates a `PlainTime` value from a total number of millisecond.
-/
@[inline]
def ofMilliseconds (millis : Millisecond.Offset) : PlainTime :=
  ofNanoseconds millis.toNanoseconds

/--
Creates a `PlainTime` value from a total number of seconds.
-/
@[inline]
def ofSeconds (secs : Second.Offset) : PlainTime :=
  ofNanoseconds secs.toNanoseconds

/--
Creates a `PlainTime` value from a total number of minutes.
-/
@[inline]
def ofMinutes (secs : Minute.Offset) : PlainTime :=
  ofNanoseconds secs.toNanoseconds

/--
Creates a `PlainTime` value from a total number of hours.
-/
@[inline]
def ofHours (hour : Hour.Offset) : PlainTime :=
  ofNanoseconds hour.toNanoseconds

/--
Adds seconds to a `PlainTime`.
-/
@[inline]
def addSeconds (time : PlainTime) (secondsToAdd : Second.Offset) : PlainTime :=
  let totalSeconds := time.toNanoseconds + secondsToAdd.toNanoseconds
  ofNanoseconds totalSeconds

/--
Subtracts seconds from a `PlainTime`.
-/
@[inline]
def subSeconds (time : PlainTime) (secondsToSub : Second.Offset) : PlainTime :=
  addSeconds time (-secondsToSub)

/--
Adds minutes to a `PlainTime`.
-/
@[inline]
def addMinutes (time : PlainTime) (minutesToAdd : Minute.Offset) : PlainTime :=
  let total := time.toNanoseconds + minutesToAdd.toNanoseconds
  ofNanoseconds total

/--
Subtracts minutes from a `PlainTime`.
-/
@[inline]
def subMinutes (time : PlainTime) (minutesToSub : Minute.Offset) : PlainTime :=
  addMinutes time (-minutesToSub)

/--
Adds hours to a `PlainTime`.
-/
@[inline]
def addHours (time : PlainTime) (hoursToAdd : Hour.Offset) : PlainTime :=
  let total := time.toNanoseconds + hoursToAdd.toNanoseconds
  ofNanoseconds total

/--
Subtracts hours from a `PlainTime`.
-/
@[inline]
def subHours (time : PlainTime) (hoursToSub : Hour.Offset) : PlainTime :=
  addHours time (-hoursToSub)

/--
Adds nanoseconds to a `PlainTime`.
-/
def addNanoseconds (time : PlainTime) (nanosToAdd : Nanosecond.Offset) : PlainTime :=
  let total := time.toNanoseconds + nanosToAdd
  ofNanoseconds total

/--
Subtracts nanoseconds from a `PlainTime`.
-/
def subNanoseconds (time : PlainTime) (nanosToSub : Nanosecond.Offset) : PlainTime :=
  addNanoseconds time (-nanosToSub)

/--
Adds milliseconds to a `PlainTime`.
-/
def addMilliseconds (time : PlainTime) (millisToAdd : Millisecond.Offset) : PlainTime :=
  let total := time.toMilliseconds + millisToAdd
  ofMilliseconds total

/--
Subtracts milliseconds from a `PlainTime`.
-/
def subMilliseconds (time : PlainTime) (millisToSub : Millisecond.Offset) : PlainTime :=
  addMilliseconds time (-millisToSub)

/--
Creates a new `PlainTime` by adjusting the `second` component to the given value.
-/
@[inline]
def withSeconds (pt : PlainTime) (second : Second.Ordinal true) : PlainTime :=
  { pt with second := second }

/--
Creates a new `PlainTime` by adjusting the `minute` component to the given value.
-/
@[inline]
def withMinutes (pt : PlainTime) (minute : Minute.Ordinal) : PlainTime :=
  { pt with minute := minute }

/--
Creates a new `PlainTime` by adjusting the milliseconds component inside the `nano` component of its `time` to the given value.
-/
@[inline]
def withMilliseconds (pt : PlainTime) (millis : Millisecond.Ordinal) : PlainTime :=
  let minorPart := pt.nanosecond.emod 1000 (by decide)
  let majorPart := millis.mul_pos 1000000 (by decide) |>.addBounds minorPart
  { pt with nanosecond := majorPart |>.expandTop (by decide) }

/--
Creates a new `PlainTime` by adjusting the `nano` component to the given value.
-/
@[inline]
def withNanoseconds (pt : PlainTime) (nano : Nanosecond.Ordinal) : PlainTime :=
  { pt with nanosecond := nano }

/--
Creates a new `PlainTime` by adjusting the `hour` component to the given value.
-/
@[inline]
def withHours (pt : PlainTime) (hour : Hour.Ordinal) : PlainTime :=
  { pt with hour := hour }

/--
`Millisecond` component of the `PlainTime`
-/
@[inline]
def millisecond (pt : PlainTime) : Millisecond.Ordinal :=
  pt.nanosecond.ediv 1000000 (by decide)

instance : HAdd PlainTime Nanosecond.Offset PlainTime where
  hAdd := addNanoseconds

instance : HSub PlainTime Nanosecond.Offset PlainTime where
  hSub := subNanoseconds

instance : HAdd PlainTime Millisecond.Offset PlainTime where
  hAdd := addMilliseconds

instance : HSub PlainTime Millisecond.Offset PlainTime where
  hSub := subMilliseconds

instance : HAdd PlainTime Second.Offset PlainTime where
  hAdd := addSeconds

instance : HSub PlainTime Second.Offset PlainTime where
  hSub := subSeconds

instance : HAdd PlainTime Minute.Offset PlainTime where
  hAdd := addMinutes

instance : HSub PlainTime Minute.Offset PlainTime where
  hSub := subMinutes

instance : HAdd PlainTime Hour.Offset PlainTime where
  hAdd := addHours

instance : HSub PlainTime Hour.Offset PlainTime where
  hSub := subHours

end PlainTime
end Time
end Std
