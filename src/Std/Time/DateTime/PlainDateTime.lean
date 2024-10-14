/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date
import Std.Time.Time
import Std.Time.Internal
import Std.Time.DateTime.Timestamp

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
Represents a date and time with components for Year, Month, Day, Hour, Minute, Second, and Nanosecond.
-/
structure PlainDateTime where

  /--
  The `Date` component of a `PlainDate`
  -/
  date : PlainDate

  /--
  The `Time` component of a `PlainTime`
  -/
  time : PlainTime

  deriving Inhabited, BEq

namespace PlainDateTime

/--
Converts a `PlainDateTime` to a `Timestamp`
-/
def toTimestampAssumingUTC (dt : PlainDateTime) : Timestamp :=
  let days := dt.date.toDaysSinceUNIXEpoch
  let nanos := days.toSeconds + dt.time.toSeconds |>.mul 1000000000
  let nanos := nanos.val + dt.time.nano.val
  Timestamp.ofNanosecondsSinceUnixEpoch (Nanosecond.Offset.ofInt nanos)

/--
Converts a UNIX `Timestamp` to a `PlainDateTime`.
-/
def ofUTCTimestamp (stamp : Timestamp) : PlainDateTime := Id.run do
  let leapYearEpoch := 11017
  let daysPer400Y := 365 * 400 + 97
  let daysPer100Y := 365 * 100 + 24
  let daysPer4Y := 365 * 4 + 1

  let nanos := stamp.toNanosecondsSinceUnixEpoch
  let secs : Second.Offset := nanos.ediv 1000000000
  let daysSinceEpoch : Day.Offset := secs.ediv 86400
  let boundedDaysSinceEpoch := daysSinceEpoch

  let mut rawDays := boundedDaysSinceEpoch - leapYearEpoch
  let mut rem := Bounded.LE.byMod secs.val 86400 (by decide)

  let ⟨remSecs, days⟩ :=
    if h : rem.val ≤ -1 then
      let remSecs := rem.truncateTop h
      let remSecs : Bounded.LE 1 86399 := remSecs.add 86400
      let rawDays := rawDays - 1
      (remSecs.expandBottom (by decide), rawDays)
    else
      let h := rem.truncateBottom (Int.not_le.mp h)
      (h, rawDays)

  let mut quadracentennialCycles := days / daysPer400Y;
  let mut remDays := days.val % daysPer400Y.val;

  if remDays < 0 then
    remDays := remDays + daysPer400Y.val
    quadracentennialCycles := quadracentennialCycles - 1

  let mut centenialCycles := remDays / daysPer100Y;

  if centenialCycles = 4 then
    centenialCycles := centenialCycles - 1

  remDays := remDays - centenialCycles * daysPer100Y
  let mut quadrennialCycles := remDays / daysPer4Y;

  if quadrennialCycles = 25 then
    quadrennialCycles := quadrennialCycles - 1

  remDays := remDays - quadrennialCycles * daysPer4Y
  let mut remYears := remDays / 365;

  if remYears = 4 then
    remYears := remYears - 1

  remDays := remDays - remYears * 365

  let mut year := 2000 + remYears + 4 * quadrennialCycles + 100 * centenialCycles + 400 * quadracentennialCycles.val
  let months := [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
  let mut mon : Fin 13 := 0;

  for monLen in months do
    mon := mon + 1;
    if remDays < monLen then
      break
    remDays := remDays - monLen

  let mday : Fin 31 := Fin.ofNat (Int.toNat remDays)

  let hmon ←
    if h₁ : mon.val > 10
      then do
        year := year + 1
        pure (Month.Ordinal.ofNat (mon.val - 10) (by omega))
      else
        pure (Month.Ordinal.ofNat (mon.val + 2) (by omega))

  let second : Bounded.LE 0 59 := remSecs.emod 60 (by decide)
  let minute : Bounded.LE 0 59 := (remSecs.ediv 60 (by decide)).emod 60 (by decide)
  let hour : Bounded.LE 0 23 := remSecs.ediv 3600 (by decide)
  let nano : Bounded.LE 0 999999999 := Bounded.LE.byEmod nanos.val 1000000000 (by decide)

  return {
    date := PlainDate.clip year hmon (Day.Ordinal.ofFin (Fin.succ mday))
    time := PlainTime.ofHourMinuteSecondsNano (leap := false) (hour.expandTop (by decide)) minute second nano
  }

/--
Creates a new `PlainDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : PlainDateTime) (days : Day.Ordinal) : PlainDateTime :=
  { dt with date := PlainDate.clip dt.date.year dt.date.month days }

/--
Creates a new `PlainDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days rolled over to the next month or year as needed.
-/
@[inline]
def withDaysRollOver (dt : PlainDateTime) (days : Day.Ordinal) : PlainDateTime :=
  { dt with date := PlainDate.rollOver dt.date.year dt.date.month days }

/--
Creates a new `PlainDateTime` by adjusting the month to the given `month` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withMonthClip (dt : PlainDateTime) (month : Month.Ordinal) : PlainDateTime :=
  { dt with date := PlainDate.clip dt.date.year month dt.date.day }

/--
Creates a new `PlainDateTime` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : PlainDateTime) (month : Month.Ordinal) : PlainDateTime :=
  { dt with date := PlainDate.rollOver dt.date.year month dt.date.day }

/--
Creates a new `PlainDateTime` by adjusting the year to the given `year` value. The month and day
remain unchanged, with any out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withYearClip (dt : PlainDateTime) (year : Year.Offset) : PlainDateTime :=
  { dt with date := PlainDate.clip year dt.date.month dt.date.day }

/--
Creates a new `PlainDateTime` by adjusting the year to the given `year` value. The month and day are rolled
over to the next valid month and day if necessary.
-/
@[inline]
def withYearRollOver (dt : PlainDateTime) (year : Year.Offset) : PlainDateTime :=
  { dt with date := PlainDate.rollOver year dt.date.month dt.date.day }

/--
Creates a new `PlainDateTime` by adjusting the `hour` component of its `time` to the given value.
-/
@[inline]
def withHours (dt : PlainDateTime) (hour : Hour.Ordinal) : PlainDateTime :=
  { dt with time := { dt.time with hour := hour } }

/--
Creates a new `PlainDateTime` by adjusting the `minute` component of its `time` to the given value.
-/
@[inline]
def withMinutes (dt : PlainDateTime) (minute : Minute.Ordinal) : PlainDateTime :=
  { dt with time := { dt.time with minute := minute } }

/--
Creates a new `PlainDateTime` by adjusting the `second` component of its `time` to the given value.
-/
@[inline]
def withSeconds (dt : PlainDateTime) (second : Sigma Second.Ordinal) : PlainDateTime :=
  { dt with time := { dt.time with second := second } }

/--
Creates a new `PlainDateTime` by adjusting the `nano` component of its `time` to the given value.
-/
@[inline]
def withNanoseconds (dt : PlainDateTime) (nano : Nanosecond.Ordinal) : PlainDateTime :=
  { dt with time := { dt.time with nano := nano } }

/--
Adds a `Day.Offset` to a `PlainDateTime`.
-/
@[inline]
def addDays (dt : PlainDateTime) (days : Day.Offset) : PlainDateTime :=
  { dt with date := dt.date.addDays days }

/--
Subtracts a `Day.Offset` from a `PlainDateTime`.
-/
@[inline]
def subDays (dt : PlainDateTime) (days : Day.Offset) : PlainDateTime :=
  { dt with date := dt.date.subDays days }

/--
Adds a `Week.Offset` to a `PlainDateTime`.
-/
@[inline]
def addWeeks (dt : PlainDateTime) (weeks : Week.Offset) : PlainDateTime :=
  { dt with date := dt.date.addWeeks weeks }

/--
Subtracts a `Week.Offset` from a `PlainDateTime`.
-/
@[inline]
def subWeeks (dt : PlainDateTime) (weeks : Week.Offset) : PlainDateTime :=
  { dt with date := dt.date.subWeeks weeks }

/--
Adds a `Month.Offset` to a `PlainDateTime`, adjusting the day to the last valid day of the resulting
month.
-/
def addMonthsClip (dt : PlainDateTime) (months : Month.Offset) : PlainDateTime :=
  { dt with date := dt.date.addMonthsClip months }

/--
Subtracts `Month.Offset` from a `PlainDateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (dt : PlainDateTime) (months : Month.Offset) : PlainDateTime :=
  { dt with date := dt.date.subMonthsClip months }

/--
Adds a `Month.Offset` to a `PlainDateTime`, rolling over excess days to the following month if needed.
-/
def addMonthsRollOver (dt : PlainDateTime) (months : Month.Offset) : PlainDateTime :=
  { dt with date := dt.date.addMonthsRollOver months }

/--
Subtracts a `Month.Offset` from a `PlainDateTime`, adjusting the day to the last valid day of the
resulting month.
-/
@[inline]
def subMonthsRollOver (dt : PlainDateTime) (months : Month.Offset) : PlainDateTime :=
  { dt with date := dt.date.subMonthsRollOver months }

/--
Adds a `Month.Offset` to a `PlainDateTime`, rolling over excess days to the following month if needed.
-/
@[inline]
def addYearsRollOver (dt : PlainDateTime) (years : Year.Offset) : PlainDateTime :=
  { dt with date := dt.date.addYearsRollOver years }

/--
Subtracts a `Month.Offset` from a `PlainDateTime`, rolling over excess days to the following month if
needed.
-/
@[inline]
def addYearsClip (dt : PlainDateTime) (years : Year.Offset) : PlainDateTime :=
  { dt with date := dt.date.addYearsClip years }

/--
Subtracts a `Year.Offset` from a `PlainDateTime`, this function rolls over any excess days into the
following month.
-/
@[inline]
def subYearsRollOver (dt : PlainDateTime) (years : Year.Offset) : PlainDateTime :=
  { dt with date := dt.date.subYearsRollOver years }

/--
Subtracts a `Year.Offset` from a `PlainDateTime`, adjusting the day to the last valid day of the
resulting month.
-/
@[inline]
def subYearsClip (dt : PlainDateTime) (years : Year.Offset) : PlainDateTime :=
  { dt with date := dt.date.subYearsClip years }


/--
Adds an `Hour.Offset` to a `PlainDateTime`, adjusting the date if the hour overflows.
-/
@[inline]
def addHours (dt : PlainDateTime) (hours : Hour.Offset) : PlainDateTime :=
  let totalSeconds := dt.time.toSeconds + hours.toSeconds
  let days := totalSeconds.ediv 86400
  let newTime := dt.time.addSeconds (hours.toSeconds)
  { dt with date := dt.date.addDays days, time := newTime }

/--
Subtracts an `Hour.Offset` from a `PlainDateTime`, adjusting the date if the hour underflows.
-/
@[inline]
def subHours (dt : PlainDateTime) (hours : Hour.Offset) : PlainDateTime :=
  addHours dt (-hours)

/--
Adds a `Minute.Offset` to a `PlainDateTime`, adjusting the hour and date if the minutes overflow.
-/
@[inline]
def addMinutes (dt : PlainDateTime) (minutes : Minute.Offset) : PlainDateTime :=
  let totalSeconds := dt.time.toSeconds + minutes.toSeconds
  let days := totalSeconds.ediv 86400
  let newTime := dt.time.addSeconds (minutes.toSeconds)
  { dt with date := dt.date.addDays days, time := newTime }

/--
Subtracts a `Minute.Offset` from a `PlainDateTime`, adjusting the hour and date if the minutes underflow.
-/
@[inline]
def subMinutes (dt : PlainDateTime) (minutes : Minute.Offset) : PlainDateTime :=
  addMinutes dt (-minutes)

/--
Adds a `Second.Offset` to a `PlainDateTime`, adjusting the minute, hour, and date if the seconds overflow.
-/
@[inline]
def addSeconds (dt : PlainDateTime) (seconds : Second.Offset) : PlainDateTime :=
  let totalSeconds := dt.time.toSeconds + seconds
  let days := totalSeconds.ediv 86400
  let newTime := dt.time.addSeconds seconds
  { dt with date := dt.date.addDays days, time := newTime }

/--
Subtracts a `Second.Offset` from a `PlainDateTime`, adjusting the minute, hour, and date if the seconds underflow.
-/
@[inline]
def subSeconds (dt : PlainDateTime) (seconds : Second.Offset) : PlainDateTime :=
  addSeconds dt (-seconds)

/--
Adds a `Nanosecond.Offset` to a `PlainDateTime`, adjusting the seconds, minutes, hours, and date if the nanoseconds overflow.
-/
@[inline]
def addNanoseconds (dt : PlainDateTime) (nanos : Nanosecond.Offset) : PlainDateTime :=
  let nano := Nanosecond.Offset.ofInt dt.time.nano.val
  let totalNanos := nano + nanos
  let extraSeconds := totalNanos.ediv 1000000000
  let nano := Bounded.LE.byEmod totalNanos.val 1000000000 (by decide)
  let newTime := dt.time.addSeconds extraSeconds
  { dt with time := { newTime with nano } }

/--
Subtracts a `Nanosecond.Offset` from a `PlainDateTime`, adjusting the seconds, minutes, hours, and date if the nanoseconds underflow.
-/
@[inline]
def subNanoseconds (dt : PlainDateTime) (nanos : Nanosecond.Offset) : PlainDateTime :=
  addNanoseconds dt (-nanos)

/--
Getter for the `Year` inside of a `PlainDateTime`.
-/
@[inline]
def year (dt : PlainDateTime) : Year.Offset :=
  dt.date.year

/--
Getter for the `Month` inside of a `PlainDateTime`.
-/
@[inline]
def month (dt : PlainDateTime) : Month.Ordinal :=
  dt.date.month

/--
Getter for the `Day` inside of a `PlainDateTime`.
-/
@[inline]
def day (dt : PlainDateTime) : Day.Ordinal :=
  dt.date.day

/--
Getter for the `Hour` inside of a `PlainDateTime`.
-/
@[inline]
def hour (dt : PlainDateTime) : Hour.Ordinal :=
  dt.time.hour

/--
Getter for the `Minute` inside of a `PlainDateTime`.
-/
@[inline]
def minute (dt : PlainDateTime) : Minute.Ordinal :=
  dt.time.minute

/--
Getter for the `Second` inside of a `PlainDateTime`.
-/
@[inline]
def second (dt : PlainDateTime) : Second.Ordinal dt.time.second.fst :=
  dt.time.second.snd

/--
Getter for the `Nanosecond.Ordinal` inside of a `PlainDateTime`.
-/
@[inline]
def nanosecond (dt : PlainDateTime) : Nanosecond.Ordinal :=
  dt.time.nano

/--
Determines the era of the given `PlainDateTime` based on its year.
-/
@[inline]
def era (date : PlainDateTime) : Year.Era :=
  date.date.era

/--
Checks if the `PlainDateTime` is in a leap year.
-/
@[inline]
def inLeapYear (date : PlainDateTime) : Bool :=
  date.year.isLeap

instance : HAdd PlainDateTime Day.Offset PlainDateTime where
  hAdd := addDays

instance : HSub PlainDateTime Day.Offset PlainDateTime where
  hSub := subDays

instance : HAdd PlainDateTime Week.Offset PlainDateTime where
  hAdd := addWeeks

instance : HSub PlainDateTime Week.Offset PlainDateTime where
  hSub := subWeeks

instance : HAdd PlainDateTime Hour.Offset PlainDateTime where
  hAdd := addHours

instance : HSub PlainDateTime Hour.Offset PlainDateTime where
  hSub := subHours

instance : HAdd PlainDateTime Minute.Offset PlainDateTime where
  hAdd := addMinutes

instance : HSub PlainDateTime Minute.Offset PlainDateTime where
  hSub := subMinutes

instance : HAdd PlainDateTime Second.Offset PlainDateTime where
  hAdd := addSeconds

instance : HSub PlainDateTime Second.Offset PlainDateTime where
  hSub := subSeconds

instance : HAdd PlainDateTime Nanosecond.Offset PlainDateTime where
  hAdd := addNanoseconds

instance : HSub PlainDateTime Nanosecond.Offset PlainDateTime where
  hSub := subNanoseconds

instance : HAdd PlainDateTime Duration PlainDateTime where
  hAdd x y := addNanoseconds x y.toNanoseconds

end PlainDateTime
end Time
end Std
