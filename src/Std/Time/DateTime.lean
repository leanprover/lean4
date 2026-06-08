/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Zoned.ZoneRules
public import Std.Time.DateTime.PlainDateTime

public section

namespace Std
namespace Time

/--
Represents a date and time with timezone information.
-/
structure DateTime where
  private mk ::

  /--
  The plain datetime component, evaluated lazily.
  -/
  date : Thunk PlainDateTime

  /--
  The corresponding timestamp for the datetime.
  -/
  timestamp : Timestamp

  /--
  The timezone rules applied to this datetime.
  -/
  rules : TimeZone.ZoneRules

  /--
  The timezone associated with this datetime.
  -/
  timezone : TimeZone

instance : Inhabited DateTime where
  default := private ⟨Thunk.mk Inhabited.default, Inhabited.default, Inhabited.default, Inhabited.default⟩

namespace DateTime

/--
Creates a new `DateTime` out of a `Timestamp` and a `ZoneRules`.
-/
@[inline]
def ofTimestamp (tm : Timestamp) (rules : TimeZone.ZoneRules) : DateTime :=
  let tz := rules.timezoneAt tm
  DateTime.mk (Thunk.mk fun _ => PlainDateTime.ofWallTime (Timestamp.toWallTime tm tz.offset)) tm rules tz

/--
Creates a new `DateTime` out of a `PlainDateTime` and a `ZoneRules`. It assumes `PlainDateTime` is
the local time.
-/
@[inline]
def ofPlainDateTime (pdt : PlainDateTime) (zr : TimeZone.ZoneRules) : DateTime :=
  let wt := pdt.toWallTime
  let ltt := zr.findLocalTimeTypeForWallTime wt
  let tz := ltt.getTimeZone
  DateTime.mk (Thunk.mk fun _ => pdt) (wt.toTimestamp tz.offset) zr tz

/--
Creates a new `DateTime` out of a `Timestamp` and a `TimeZone`.
-/
@[inline]
def ofTimestampWithZone (tm : Timestamp) (tz : TimeZone) : DateTime :=
  ofTimestamp tm (TimeZone.ZoneRules.ofTimeZone tz)

/--
Creates a new `DateTime` out of a `PlainDateTime` and a `TimeZone`. It assumes `PlainDateTime` is
the local time.
-/
@[inline]
def ofPlainDateTimeWithZone (tm : PlainDateTime) (tz : TimeZone) : DateTime :=
  ofPlainDateTime tm (TimeZone.ZoneRules.ofTimeZone tz)

/--
Creates a new `Timestamp` out of a `DateTime`.
-/
@[inline]
def toTimestamp (date : DateTime) : Timestamp :=
  date.timestamp

/--
Changes the `ZoneRules` to a new one.
-/
@[inline]
def convertZoneRules (date : DateTime) (tz₁ : TimeZone.ZoneRules) : DateTime :=
  ofTimestamp date.toTimestamp tz₁

/--
Converts a `DateTime` to a `PlainDateTime`
-/
@[inline]
def toPlainDateTime (dt : DateTime) : PlainDateTime :=
  dt.date.get

/--
Getter for the `PlainTime` inside of a `DateTime`
-/
@[inline]
def time (zdt : DateTime) : PlainTime :=
  zdt.date.get.time

/--
Getter for the `Year` inside of a `DateTime`
-/
@[inline]
def year (zdt : DateTime) : Year.Offset :=
  zdt.date.get.year

/--
Getter for the `Month` inside of a `DateTime`
-/
@[inline]
def month (zdt : DateTime) : Month.Ordinal :=
  zdt.date.get.month

/--
Getter for the `Day` inside of a `DateTime`
-/
@[inline]
def day (zdt : DateTime) : Day.Ordinal :=
  zdt.date.get.day

/--
Getter for the `Hour` inside of a `DateTime`
-/
@[inline]
def hour (zdt : DateTime) : Hour.Ordinal :=
  zdt.date.get.time.hour

/--
Getter for the `Minute` inside of a `DateTime`
-/
@[inline]
def minute (zdt : DateTime) : Minute.Ordinal :=
  zdt.date.get.minute

/--
Getter for the `Second` inside of a `DateTime`
-/
@[inline]
def second (zdt : DateTime) : Second.Ordinal true :=
  zdt.date.get.time.second

/--
Getter for the `Millisecond` inside of a `DateTime`.
-/
@[inline]
def millisecond (dt : DateTime) : Millisecond.Ordinal :=
  dt.date.get.time.millisecond

/--
Getter for the `Nanosecond` inside of a `DateTime`
-/
@[inline]
def nanosecond (zdt : DateTime) : Nanosecond.Ordinal :=
  zdt.date.get.time.nanosecond

/--
Getter for the `TimeZone.Offset` inside of a `DateTime`
-/
@[inline]
def offset (zdt : DateTime) : TimeZone.Offset :=
  zdt.timezone.offset

/--
Returns the weekday.
-/
@[inline]
def weekday (zdt : DateTime) : Weekday :=
  zdt.date.get.weekday

/--
Transforms a tuple of a `DateTime` into a `Day.Ordinal.OfYear`.
-/
@[inline]
def dayOfYear (date : DateTime) : Day.Ordinal.OfYear date.date.get.date.year.isLeap :=
  ValidDate.dayOfYear ⟨(date.date.get.date.month, date.date.get.date.day), date.date.get.date.valid⟩

/--
Determines the week of the year for the given `DateTime`, using `firstDay` as the start of the week.
-/
@[inline]
def weekOfYear (date : DateTime) (firstDay : Weekday := .monday) : Week.Ordinal :=
  date.date.get.weekOfYear firstDay

/--
Returns the week-based year for the given `DateTime`, using `firstDay` as the start of the week.
The week-based year may differ from the calendar year for dates near the start or end of the year.
-/
@[inline]
def weekYear (date : DateTime) (firstDay : Weekday := .monday) : Year.Offset :=
  date.date.get.weekYear firstDay

/--
Returns the unaligned week of the month for a `DateTime` (day divided by 7, plus 1).
-/
def weekOfMonth (date : DateTime) : Internal.Bounded.LE 1 5 :=
  date.date.get.weekOfMonth

/--
Determines the week of the month for the given `DateTime`, using `firstDay` as the start of the week.
-/
@[inline]
def alignedWeekOfMonth (date : DateTime) (firstDay : Weekday := .monday) : Week.Ordinal.OfMonth :=
  date.date.get.alignedWeekOfMonth firstDay

/--
Determines the quarter of the year for the given `DateTime`.
-/
@[inline]
def quarter (date : DateTime) : Internal.Bounded.LE 1 4 :=
  date.date.get.quarter

/--
Add `Day.Offset` to a `DateTime`.
-/
def addDays (dt : DateTime) (days : Day.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp + days) dt.rules

/--
Subtract `Day.Offset` from a `DateTime`.
-/
def subDays (dt : DateTime) (days : Day.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp - days) dt.rules

/--
Add `Week.Offset` to a `DateTime`.
-/
def addWeeks (dt : DateTime) (weeks : Week.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp + weeks) dt.rules

/--
Subtract `Week.Offset` from a `DateTime`.
-/
def subWeeks (dt : DateTime) (weeks : Week.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp - weeks) dt.rules

/--
Add `Month.Offset` to a `DateTime`, clipping to the last valid day.
-/
def addMonthsClip (dt : DateTime) (months : Month.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addMonthsClip months) dt.rules

/--
Subtract `Month.Offset` from a `DateTime`, clipping to the last valid day.
-/
def subMonthsClip (dt : DateTime) (months : Month.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subMonthsClip months) dt.rules

/--
Add `Month.Offset` to a `DateTime`, rolling over excess days.
-/
def addMonthsRollOver (dt : DateTime) (months : Month.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addMonthsRollOver months) dt.rules

/--
Subtract `Month.Offset` from a `DateTime`, rolling over excess days.
-/
def subMonthsRollOver (dt : DateTime) (months : Month.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subMonthsRollOver months) dt.rules

/--
Add `Year.Offset` to a `DateTime`, rolling over excess days.
-/
def addYearsRollOver (dt : DateTime) (years : Year.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addYearsRollOver years) dt.rules

/--
Add `Year.Offset` to a `DateTime`, clipping to the last valid day.
-/
def addYearsClip (dt : DateTime) (years : Year.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addYearsClip years) dt.rules

/--
Subtract `Year.Offset` from a `DateTime`, clipping to the last valid day.
-/
def subYearsClip (dt : DateTime) (years : Year.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subYearsClip years) dt.rules

/--
Subtract `Year.Offset` from a `DateTime`, rolling over excess days.
-/
def subYearsRollOver (dt : DateTime) (years : Year.Offset) : DateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subYearsRollOver years) dt.rules

/--
Add `Hour.Offset` to a `DateTime`.
-/
def addHours (dt : DateTime) (hours : Hour.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp + hours) dt.rules

/--
Subtract `Hour.Offset` from a `DateTime`.
-/
def subHours (dt : DateTime) (hours : Hour.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp - hours) dt.rules
/--
Add `Minute.Offset` to a `DateTime`.
-/
def addMinutes (dt : DateTime) (minutes : Minute.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp + minutes) dt.rules

/--
Subtract `Minute.Offset` from a `DateTime`.
-/
def subMinutes (dt : DateTime) (minutes : Minute.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp - minutes) dt.rules
/--
Add `Millisecond.Offset` to a `DateTime`.
-/
@[inline]
def addMilliseconds (dt : DateTime) (milliseconds : Millisecond.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp + milliseconds) dt.rules

/--
Subtract `Millisecond.Offset` from a `DateTime`.
-/
@[inline]
def subMilliseconds (dt : DateTime) (milliseconds : Millisecond.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp - milliseconds) dt.rules
/--
Add `Second.Offset` to a `DateTime`.
-/
def addSeconds (dt : DateTime) (seconds : Second.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp + seconds) dt.rules

/--
Subtract `Second.Offset` from a `DateTime`.
-/
def subSeconds (dt : DateTime) (seconds : Second.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp - seconds) dt.rules
/--
Add `Nanosecond.Offset` to a `DateTime`.
-/
def addNanoseconds (dt : DateTime) (nanoseconds : Nanosecond.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp + nanoseconds) dt.rules

/--
Subtract `Nanosecond.Offset` from a `DateTime`.
-/
def subNanoseconds (dt : DateTime) (nanoseconds : Nanosecond.Offset) : DateTime :=
  .ofTimestamp (dt.timestamp - nanoseconds) dt.rules
/--
Determines the era of the given `DateTime` based on its year.
-/
@[inline]
def era (date : DateTime) : Year.Era :=
  date.date.get.era

/--
Sets the `DateTime` to the specified `desiredWeekday`.
-/
def withWeekday (dt : DateTime) (desiredWeekday : Weekday) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withWeekday desiredWeekday) dt.rules

/--
Creates a new `DateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : DateTime) (days : Day.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withDaysClip days) dt.rules

/--
Creates a new `DateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days rolled over to the next month or year as needed.
-/
@[inline]
def withDaysRollOver (dt : DateTime) (days : Day.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withDaysRollOver days) dt.rules

/--
Creates a new `DateTime` by adjusting the month to the given `month` value.
The day remains unchanged, and any invalid days for the new month will be handled according to the `clip` behavior.
-/
@[inline]
def withMonthClip (dt : DateTime) (month : Month.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMonthClip month) dt.rules

/--
Creates a new `DateTime` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : DateTime) (month : Month.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMonthRollOver month) dt.rules

/--
Creates a new `DateTime` by adjusting the year to the given `year` value. The month and day remain unchanged,
and any invalid days for the new year will be handled according to the `clip` behavior.
-/
@[inline]
def withYearClip (dt : DateTime) (year : Year.Offset) : DateTime :=
  let date := dt.date.get

  .ofPlainDateTime (date.withYearClip year) dt.rules

/--
Creates a new `DateTime` by adjusting the year to the given `year` value. The month and day are rolled
over to the next valid month and day if necessary.
-/
@[inline]
def withYearRollOver (dt : DateTime) (year : Year.Offset) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withYearRollOver year) dt.rules

/--
Creates a new `DateTime` by adjusting the `hour` component.
-/
@[inline]
def withHours (dt : DateTime) (hour : Hour.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withHours hour) dt.rules

/--
Creates a new `DateTime` by adjusting the `minute` component.
-/
@[inline]
def withMinutes (dt : DateTime) (minute : Minute.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMinutes minute) dt.rules

/--
Creates a new `DateTime` by adjusting the `second` component.
-/
@[inline]
def withSeconds (dt : DateTime) (second : Second.Ordinal true) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withSeconds second) dt.rules

/--
Creates a new `DateTime` by adjusting the `nano` component with a new `millis` that will set
in the millisecond scale.
-/
@[inline]
def withMilliseconds (dt : DateTime) (millis : Millisecond.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMilliseconds millis) dt.rules

/--
Creates a new `DateTime` by adjusting the `nano` component.
-/
@[inline]
def withNanoseconds (dt : DateTime) (nano : Nanosecond.Ordinal) : DateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withNanoseconds nano) dt.rules

/--
Checks if the `DateTime` is in a leap year.
-/
def inLeapYear (date : DateTime) : Bool :=
  date.year.isLeap

/--
Returns the local (civil) date of the `DateTime` as a `Day.Offset` relative to 1970-01-01.
-/
def toEpochDay (date : DateTime) : Day.Offset :=
  date.date.get.toEpochDay

/--
Creates a `DateTime` from a local date given as a `Day.Offset` relative to 1970-01-01, a
`PlainTime`, and `ZoneRules`. The day offset is interpreted as a local (civil) date, not UTC.
-/
@[inline]
def ofEpochDay (days : Day.Offset) (time : PlainTime) (zt : TimeZone.ZoneRules) : DateTime :=
  DateTime.ofPlainDateTime (PlainDateTime.ofEpochDay days time) zt

instance : HAdd DateTime Day.Offset DateTime where
  hAdd := addDays

instance : HSub DateTime Day.Offset DateTime where
  hSub := subDays

instance : HAdd DateTime Week.Offset DateTime where
  hAdd := addWeeks

instance : HSub DateTime Week.Offset DateTime where
  hSub := subWeeks

instance : HAdd DateTime Hour.Offset DateTime where
  hAdd := addHours

instance : HSub DateTime Hour.Offset DateTime where
  hSub := subHours

instance : HAdd DateTime Minute.Offset DateTime where
  hAdd := addMinutes

instance : HSub DateTime Minute.Offset DateTime where
  hSub := subMinutes

instance : HAdd DateTime Second.Offset DateTime where
  hAdd := addSeconds

instance : HSub DateTime Second.Offset DateTime where
  hSub := subSeconds

instance : HAdd DateTime Millisecond.Offset DateTime where
  hAdd := addMilliseconds

instance : HSub DateTime Millisecond.Offset DateTime where
  hSub := subMilliseconds

instance : HAdd DateTime Nanosecond.Offset DateTime where
  hAdd := addNanoseconds

instance : HSub DateTime Nanosecond.Offset DateTime where
  hSub := subNanoseconds

instance : HSub DateTime DateTime Duration where
  hSub x y := x.toTimestamp - y.toTimestamp

instance : HAdd DateTime Duration DateTime where
  hAdd x y := x.addNanoseconds y.toNanoseconds

instance : HSub DateTime Duration DateTime where
  hSub x y := x.subNanoseconds y.toNanoseconds

end DateTime
end Time
end Std
