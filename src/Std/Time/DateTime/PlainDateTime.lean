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

  deriving Inhabited, BEq, Repr

namespace PlainDateTime

/--
Converts a `PlainDateTime` to a `Timestamp`
-/
def toTimestampAssumingUTC (dt : PlainDateTime) : Timestamp :=
  let days := dt.date.toDaysSinceUNIXEpoch
  let nanos := days.toSeconds + dt.time.toSeconds |>.mul 1000000000
  let nanos := nanos.val + dt.time.nanosecond.val
  Timestamp.ofNanosecondsSinceUnixEpoch (Nanosecond.Offset.ofInt nanos)

/--
Converts a `Timestamp` to a `PlainDateTime`.
-/
def ofTimestampAssumingUTC (stamp : Timestamp) : PlainDateTime := Id.run do
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

  let mut quadracentennialCycles := days.val / daysPer400Y;
  let mut remDays := days.val % daysPer400Y;

  if remDays < 0 then
    remDays := remDays + daysPer400Y
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

  let mut year := 2000 + remYears + 4 * quadrennialCycles + 100 * centenialCycles + 400 * quadracentennialCycles
  let months := [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 29];
  let mut mon : Fin 13 := 0;

  for monLen in months do
    mon := mon + 1;
    if remDays < monLen then
      break
    remDays := remDays - monLen

  let mday : Fin 31 := Fin.ofNat' _ (Int.toNat remDays)

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
    date := PlainDate.ofYearMonthDayClip year hmon (Day.Ordinal.ofFin (Fin.succ mday))
    time := PlainTime.ofHourMinuteSecondsNano (leap := false) (hour.expandTop (by decide)) minute second nano
  }

/--
Converts a `PlainDateTime` to the number of days since the UNIX epoch.
-/
@[inline]
def toDaysSinceUNIXEpoch (pdt : PlainDateTime) : Day.Offset :=
  pdt.date.toDaysSinceUNIXEpoch

/--
Converts a `PlainDateTime` to the number of days since the UNIX epoch.
-/
@[inline]
def ofDaysSinceUNIXEpoch (days : Day.Offset) (time : PlainTime) : PlainDateTime :=
  PlainDateTime.mk (PlainDate.ofDaysSinceUNIXEpoch days) time

/--
Sets the `PlainDateTime` to the specified `desiredWeekday`.
-/
def withWeekday (dt : PlainDateTime) (desiredWeekday : Weekday) : PlainDateTime :=
  { dt with date := PlainDate.withWeekday dt.date desiredWeekday }

/--
Creates a new `PlainDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : PlainDateTime) (days : Day.Ordinal) : PlainDateTime :=
  { dt with date := PlainDate.ofYearMonthDayClip dt.date.year dt.date.month days }

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
  { dt with date := PlainDate.ofYearMonthDayClip dt.date.year month dt.date.day }

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
  { dt with date := PlainDate.ofYearMonthDayClip year dt.date.month dt.date.day }

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
Creates a new `PlainDateTime` by adjusting the milliseconds component inside the `nano` component of its `time` to the given value.
-/
@[inline]
def withMilliseconds (dt : PlainDateTime) (millis : Millisecond.Ordinal) : PlainDateTime :=
  { dt with time := dt.time.withMilliseconds millis }

/--
Creates a new `PlainDateTime` by adjusting the `nano` component of its `time` to the given value.
-/
@[inline]
def withNanoseconds (dt : PlainDateTime) (nano : Nanosecond.Ordinal) : PlainDateTime :=
  { dt with time := dt.time.withNanoseconds nano }

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
Adds a `Millisecond.Offset` to a `PlainDateTime`, adjusting the second, minute, hour, and date if the milliseconds overflow.
-/
@[inline]
def addMilliseconds (dt : PlainDateTime) (milliseconds : Millisecond.Offset) : PlainDateTime :=
  let totalMilliseconds := dt.time.toMilliseconds + milliseconds
  let days := totalMilliseconds.ediv 86400000 -- 86400000 ms in a day
  let newTime := dt.time.addMilliseconds milliseconds
  { dt with date := dt.date.addDays days, time := newTime }

/--
Subtracts a `Millisecond.Offset` from a `PlainDateTime`, adjusting the second, minute, hour, and date if the milliseconds underflow.
-/
@[inline]
def subMilliseconds (dt : PlainDateTime) (milliseconds : Millisecond.Offset) : PlainDateTime :=
  addMilliseconds dt (-milliseconds)

/--
Adds a `Nanosecond.Offset` to a `PlainDateTime`, adjusting the seconds, minutes, hours, and date if the nanoseconds overflow.
-/
@[inline]
def addNanoseconds (dt : PlainDateTime) (nanos : Nanosecond.Offset) : PlainDateTime :=
  let nano := Nanosecond.Offset.ofInt dt.time.nanosecond.val
  let totalNanos := nano + nanos
  let extraSeconds := totalNanos.ediv 1000000000
  let nanosecond := Bounded.LE.byEmod totalNanos.val 1000000000 (by decide)
  let newTime := dt.time.addSeconds extraSeconds
  { dt with time := { newTime with nanosecond } }

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
Getter for the `Weekday` inside of a `PlainDateTime`.
-/
@[inline]
def weekday (dt : PlainDateTime) : Weekday :=
  dt.date.weekday

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
Getter for the `Millisecond` inside of a `PlainDateTime`.
-/
@[inline]
def millisecond (dt : PlainDateTime) : Millisecond.Ordinal :=
  dt.time.millisecond

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
  dt.time.nanosecond

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

/--
Determines the week of the year for the given `PlainDateTime`.
-/
@[inline]
def weekOfYear (date : PlainDateTime) : Week.Ordinal :=
  date.date.weekOfYear

/--
Returns the unaligned week of the month for a `PlainDateTime` (day divided by 7, plus 1).
-/
def weekOfMonth (date : PlainDateTime) : Bounded.LE 1 5 :=
  date.date.weekOfMonth

/--
Determines the week of the month for the given `PlainDateTime`. The week of the month is calculated based
on the day of the month and the weekday. Each week starts on Monday because the entire library is
based on the Gregorian Calendar.
-/
@[inline]
def alignedWeekOfMonth (date : PlainDateTime) : Week.Ordinal.OfMonth :=
  date.date.alignedWeekOfMonth

/--
Transforms a tuple of a `PlainDateTime` into a `Day.Ordinal.OfYear`.
-/
@[inline]
def dayOfYear (date : PlainDateTime) : Day.Ordinal.OfYear date.year.isLeap :=
  ValidDate.dayOfYear ⟨(date.month, date.day), date.date.valid⟩

/--
Determines the quarter of the year for the given `PlainDateTime`.
-/
@[inline]
def quarter (date : PlainDateTime) : Bounded.LE 1 4 :=
  date.date.quarter

/--
Combines a `PlainDate` and `PlainTime` into a `PlainDateTime`.
-/
@[inline]
def atTime : PlainDate → PlainTime → PlainDateTime :=
  PlainDateTime.mk

/--
Combines a `PlainTime` and `PlainDate` into a `PlainDateTime`.
-/
@[inline]
def atDate (time: PlainTime) (date: PlainDate) : PlainDateTime :=
  PlainDateTime.mk date time

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

instance : HAdd PlainDateTime Millisecond.Offset PlainDateTime where
  hAdd := addMilliseconds

instance : HSub PlainDateTime Millisecond.Offset PlainDateTime where
  hSub := addMilliseconds

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
namespace PlainDate

/--
Combines a `PlainDate` and `PlainTime` into a `PlainDateTime`.
-/
@[inline]
def atTime : PlainDate → PlainTime → PlainDateTime :=
  PlainDateTime.mk

end PlainDate
namespace PlainTime

/--
Combines a `PlainTime` and `PlainDate` into a `PlainDateTime`.
-/
@[inline]
def atDate (time: PlainTime) (date: PlainDate) : PlainDateTime :=
  PlainDateTime.mk date time

end PlainTime
end Time
end Std
