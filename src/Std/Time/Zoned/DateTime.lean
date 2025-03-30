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
open Internal

set_option linter.all true

/--
Represents a specific point in time associated with a `TimeZone`.
-/
structure DateTime (tz : TimeZone) where
  private mk ::

  /--
  `Timestamp` represents the exact moment in time. It's a UTC related `Timestamp`.
  -/
  timestamp : Timestamp

  /--
  `Date` is a `Thunk` containing the `PlainDateTime` that represents the local date and time, it's
  used for accessing data like `day` and `month` without having to recompute the data everytime.
  -/
  date : Thunk PlainDateTime

instance : BEq (DateTime tz) where
  beq x y := x.timestamp == y.timestamp

instance : Ord (DateTime tz) where
  compare := compareOn (·.timestamp)

instance : TransOrd (DateTime tz) := inferInstanceAs <| TransCmp (compareOn _)

instance : LawfulBEqOrd (DateTime tz) where
  compare_eq_iff_beq := LawfulBEqOrd.compare_eq_iff_beq (α := Timestamp)

namespace DateTime

/--
Creates a new `DateTime` out of a `Timestamp` that is in a `TimeZone`.
-/
@[inline]
def ofTimestamp (tm : Timestamp) (tz : TimeZone) : DateTime tz :=
  DateTime.mk tm (Thunk.mk fun _ => tm.toPlainDateTimeAssumingUTC |>.addSeconds tz.toSeconds)

instance : Inhabited (DateTime tz) where
  default := ofTimestamp Inhabited.default tz

/--
Converts a `DateTime` to the number of days since the UNIX epoch.
-/
def toDaysSinceUNIXEpoch (date : DateTime tz) : Day.Offset :=
  date.date.get.toDaysSinceUNIXEpoch

/--
Creates a `Timestamp` out of a `DateTime`.
-/
@[inline]
def toTimestamp (date : DateTime tz) : Timestamp :=
  date.timestamp

/--
Changes the `TimeZone` to a new one.
-/
@[inline]
def convertTimeZone (date : DateTime tz) (tz₁ : TimeZone) : DateTime tz₁ :=
  ofTimestamp date.timestamp tz₁

/--
Creates a new `DateTime` out of a `PlainDateTime`. It assumes that the `PlainDateTime` is relative
to UTC.
-/
@[inline]
def ofPlainDateTimeAssumingUTC (date : PlainDateTime) (tz : TimeZone) : DateTime tz :=
  let tm := Timestamp.ofPlainDateTimeAssumingUTC date
  DateTime.mk tm (Thunk.mk fun _ => date.addSeconds tz.toSeconds)

/--
Creates a new `DateTime` from a `PlainDateTime`, assuming that the `PlainDateTime`
is relative to the given `TimeZone`.
-/
@[inline]
def ofPlainDateTime (date : PlainDateTime) (tz : TimeZone) : DateTime tz :=
  let tm := date.subSeconds tz.toSeconds
  DateTime.mk (Timestamp.ofPlainDateTimeAssumingUTC tm) (Thunk.mk fun _ => date)

/--
Add `Hour.Offset` to a `DateTime`.
-/
@[inline]
def addHours (dt : DateTime tz) (hours : Hour.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addHours hours) tz

/--
Subtract `Hour.Offset` from a `DateTime`.
-/
@[inline]
def subHours (dt : DateTime tz) (hours : Hour.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subHours hours) tz

/--
Add `Minute.Offset` to a `DateTime`.
-/
@[inline]
def addMinutes (dt : DateTime tz) (minutes : Minute.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addMinutes minutes) tz

/--
Subtract `Minute.Offset` from a `DateTime`.
-/
@[inline]
def subMinutes (dt : DateTime tz) (minutes : Minute.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subMinutes minutes) tz

/--
Add `Second.Offset` to a `DateTime`.
-/
@[inline]
def addSeconds (dt : DateTime tz) (seconds : Second.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addSeconds seconds) tz

/--
Subtract `Second.Offset` from a `DateTime`.
-/
@[inline]
def subSeconds (dt : DateTime tz) (seconds : Second.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subSeconds seconds) tz

/--
Add `Millisecond.Offset` to a `DateTime`.
-/
@[inline]
def addMilliseconds (dt : DateTime tz) (milliseconds : Millisecond.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addMilliseconds milliseconds) tz

/--
Subtract `Millisecond.Offset` from a `DateTime`.
-/
@[inline]
def subMilliseconds (dt : DateTime tz) (milliseconds : Millisecond.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subMilliseconds milliseconds) tz

/--
Add `Nanosecond.Offset` to a `DateTime`.
-/
@[inline]
def addNanoseconds (dt : DateTime tz) (nanoseconds : Nanosecond.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addNanoseconds nanoseconds) tz

/--
Subtract `Nanosecond.Offset` from a `DateTime`.
-/
@[inline]
def subNanoseconds (dt : DateTime tz) (nanoseconds : Nanosecond.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subNanoseconds nanoseconds) tz

/--
Add `Day.Offset` to a `DateTime`.
-/
@[inline]
def addDays (dt : DateTime tz) (days : Day.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addDays days) tz

/--
Subtracts `Day.Offset` to a `DateTime`.
-/
@[inline]
def subDays (dt : DateTime tz) (days : Day.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subDays days) tz

/--
Add `Week.Offset` to a `DateTime`.
-/
@[inline]
def addWeeks (dt : DateTime tz) (weeks : Week.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addWeeks weeks) tz

/--
Subtracts `Week.Offset` to a `DateTime`.
-/
@[inline]
def subWeeks (dt : DateTime tz) (weeks : Week.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subWeeks weeks) tz

/--
Add `Month.Offset` to a `DateTime`, it clips the day to the last valid day of that month.
-/
def addMonthsClip (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addMonthsClip months) tz

/--
Subtracts `Month.Offset` from a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subMonthsClip months) tz

/--
Add `Month.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
def addMonthsRollOver (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addMonthsRollOver months) tz

/--
Subtract `Month.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def subMonthsRollOver (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subMonthsRollOver months) tz

/--
Add `Year.Offset` to a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def addYearsRollOver (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addYearsRollOver years) tz

/--
Add `Year.Offset` to a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def addYearsClip (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.addYearsClip years) tz

/--
Subtract `Year.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def subYearsRollOver (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subYearsRollOver years) tz

/--
Subtract `Year.Offset` from to a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subYearsClip (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.subYearsClip years) tz

/--
Creates a new `DateTime tz` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : DateTime tz) (days : Day.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withDaysClip days) tz

/--
Creates a new `DateTime tz` by adjusting the day of the month to the given `days` value, with any
out-of-range days rolled over to the next month or year as needed.
-/
@[inline]
def withDaysRollOver (dt : DateTime tz) (days : Day.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withDaysRollOver days) tz

/--
Creates a new `DateTime tz` by adjusting the month to the given `month` value.
The day remains unchanged, and any invalid days for the new month will be handled according to the `clip` behavior.
-/
@[inline]
def withMonthClip (dt : DateTime tz) (month : Month.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withMonthClip month) tz

/--
Creates a new `DateTime tz` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : DateTime tz) (month : Month.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withMonthRollOver month) tz

/--
Creates a new `DateTime tz` by adjusting the year to the given `year` value. The month and day remain unchanged,
and any invalid days for the new year will be handled according to the `clip` behavior.
-/
@[inline]
def withYearClip (dt : DateTime tz) (year : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withYearClip year) tz

/--
Creates a new `DateTime tz` by adjusting the year to the given `year` value. The month and day are rolled
over to the next valid month and day if necessary.
-/
@[inline]
def withYearRollOver (dt : DateTime tz) (year : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withYearRollOver year) tz

/--
Creates a new `DateTime tz` by adjusting the `hour` component.
-/
@[inline]
def withHours (dt : DateTime tz) (hour : Hour.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withHours hour) tz

/--
Creates a new `DateTime tz` by adjusting the `minute` component.
-/
@[inline]
def withMinutes (dt : DateTime tz) (minute : Minute.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withMinutes minute) tz

/--
Creates a new `DateTime tz` by adjusting the `second` component.
-/
@[inline]
def withSeconds (dt : DateTime tz) (second : Second.Ordinal true) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withSeconds second) tz

/--
Creates a new `DateTime tz` by adjusting the `nano` component.
-/
@[inline]
def withNanoseconds (dt : DateTime tz) (nano : Nanosecond.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withNanoseconds nano) tz

/--
Creates a new `DateTime tz` by adjusting the `millisecond` component.
-/
@[inline]
def withMilliseconds (dt : DateTime tz) (milli : Millisecond.Ordinal) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withMilliseconds milli) tz

/--
Converts a `Timestamp` to a `PlainDateTime`
-/
@[inline]
def toPlainDateTime (dt : DateTime tz) : PlainDateTime :=
  dt.date.get

/--
Getter for the `Year` inside of a `DateTime`
-/
@[inline]
def year (dt : DateTime tz) : Year.Offset :=
  dt.date.get.year

/--
Getter for the `Month` inside of a `DateTime`
-/
@[inline]
def month (dt : DateTime tz) : Month.Ordinal :=
  dt.date.get.month

/--
Getter for the `Day` inside of a `DateTime`
-/
@[inline]
def day (dt : DateTime tz) : Day.Ordinal :=
  dt.date.get.day

/--
Getter for the `Hour` inside of a `DateTime`
-/
@[inline]
def hour (dt : DateTime tz) : Hour.Ordinal :=
  dt.date.get.hour

/--
Getter for the `Minute` inside of a `DateTime`
-/
@[inline]
def minute (dt : DateTime tz) : Minute.Ordinal :=
  dt.date.get.minute

/--
Getter for the `Second` inside of a `DateTime`
-/
@[inline]
def second (dt : DateTime tz) : Second.Ordinal true :=
  dt.date.get.second

/--
Getter for the `Milliseconds` inside of a `DateTime`
-/
@[inline]
def millisecond (dt : DateTime tz) : Millisecond.Ordinal :=
  dt.date.get.time.nanosecond.emod 1000 (by decide)

/--
Getter for the `Nanosecond` inside of a `DateTime`
-/
@[inline]
def nanosecond (dt : DateTime tz) : Nanosecond.Ordinal :=
  dt.date.get.time.nanosecond

/--
Gets the `Weekday` of a DateTime.
-/
@[inline]
def weekday (dt : DateTime tz) : Weekday :=
  dt.date.get.date.weekday

/--
Determines the era of the given `DateTime` based on its year.
-/
def era (date : DateTime tz) : Year.Era :=
  date.year.era

/--
Sets the `DateTime` to the specified `desiredWeekday`.
-/
def withWeekday (dt : DateTime tz) (desiredWeekday : Weekday) : DateTime tz :=
  ofPlainDateTime (dt.date.get.withWeekday desiredWeekday) tz

/--
Checks if the `DateTime` is in a leap year.
-/
def inLeapYear (date : DateTime tz) : Bool :=
  date.year.isLeap

/--
Determines the ordinal day of the year for the given `DateTime`.
-/
def dayOfYear (date : DateTime tz) : Day.Ordinal.OfYear date.year.isLeap :=
  ValidDate.dayOfYear ⟨⟨date.month, date.day⟩, date.date.get.date.valid⟩

/--
Determines the week of the year for the given `DateTime`.
-/
@[inline]
def weekOfYear (date : DateTime tz) : Week.Ordinal :=
  date.date.get.weekOfYear

/--
Returns the unaligned week of the month for a `DateTime` (day divided by 7, plus 1).
-/
def weekOfMonth (date : DateTime tz) : Bounded.LE 1 5 :=
  date.date.get.weekOfMonth

/--
Determines the week of the month for the given `DateTime`. The week of the month is calculated based
on the day of the month and the weekday. Each week starts on Monday because the entire library is
based on the Gregorian Calendar.
-/
@[inline]
def alignedWeekOfMonth (date : DateTime tz) : Week.Ordinal.OfMonth :=
  date.date.get.alignedWeekOfMonth

/--
Determines the quarter of the year for the given `DateTime`.
-/
@[inline]
def quarter (date : DateTime tz) : Bounded.LE 1 4 :=
  date.date.get.quarter

/--
Getter for the `PlainTime` inside of a `DateTime`
-/
@[inline]
def time (zdt : DateTime tz) : PlainTime :=
  zdt.date.get.time

/--
Converts a `DateTime` to the number of days since the UNIX epoch.
-/
@[inline]
def ofDaysSinceUNIXEpoch (days : Day.Offset) (time : PlainTime) (tz : TimeZone) : DateTime tz :=
  DateTime.ofPlainDateTime (PlainDateTime.ofDaysSinceUNIXEpoch days time) tz

instance : HAdd (DateTime tz) (Day.Offset) (DateTime tz) where
  hAdd := addDays

instance : HSub (DateTime tz) (Day.Offset) (DateTime tz) where
  hSub := subDays

instance : HAdd (DateTime tz) (Week.Offset) (DateTime tz) where
  hAdd := addWeeks

instance : HSub (DateTime tz) (Week.Offset) (DateTime tz) where
  hSub := subWeeks

instance : HAdd (DateTime tz) (Hour.Offset) (DateTime tz) where
  hAdd := addHours

instance : HSub (DateTime tz) (Hour.Offset) (DateTime tz) where
  hSub := subHours

instance : HAdd (DateTime tz) (Minute.Offset) (DateTime tz) where
  hAdd := addMinutes

instance : HSub (DateTime tz) (Minute.Offset) (DateTime tz) where
  hSub := subMinutes

instance : HAdd (DateTime tz) (Second.Offset) (DateTime tz) where
  hAdd := addSeconds

instance : HSub (DateTime tz) (Second.Offset) (DateTime tz) where
  hSub := subSeconds

instance : HAdd (DateTime tz) (Millisecond.Offset) (DateTime tz) where
  hAdd := addMilliseconds

instance : HSub (DateTime tz) (Millisecond.Offset) (DateTime tz) where
  hSub := subMilliseconds

instance : HAdd (DateTime tz) (Nanosecond.Offset) (DateTime tz) where
  hAdd := addNanoseconds

instance : HSub (DateTime tz) (Nanosecond.Offset) (DateTime tz) where
  hSub := subNanoseconds

instance : HSub (DateTime tz) (DateTime tz₁) Duration where
  hSub x y := x.toTimestamp - y.toTimestamp

instance : HAdd (DateTime tz) Duration (DateTime tz) where
  hAdd x y := x.addNanoseconds y.toNanoseconds

instance : HSub (DateTime tz) Duration (DateTime tz) where
  hSub x y := x.subNanoseconds y.toNanoseconds

end DateTime
end Time
end Std
