/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
module

prelude
public import Std.Time.Zoned.DateTime
public import Std.Time.Zoned.ZoneRules
import all Std.Time.DateTime.PlainDateTime

public section

namespace Std
namespace Time

-- TODO (@kim-em): re-enable this once there is a mechanism to exclude `linter.indexVariables`.
-- set_option linter.all true

/--
Represents a date and time with timezone information.
-/
structure ZonedDateTime where
  private mk::

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

instance : Inhabited ZonedDateTime where
  default := private ⟨Thunk.mk Inhabited.default, Inhabited.default, Inhabited.default, Inhabited.default⟩

namespace ZonedDateTime
open DateTime

/--
Creates a new `ZonedDateTime` out of a `Timestamp` and a `ZoneRules`.
-/
@[inline]
def ofTimestamp (tm : Timestamp) (rules : TimeZone.ZoneRules) : ZonedDateTime :=
  let tz := rules.timezoneAt tm
  ZonedDateTime.mk (Thunk.mk fun _ => PlainDateTime.ofWallTime (Timestamp.toWallTime tm tz.offset)) tm rules tz

/--
Creates a new `ZonedDateTime` out of a `PlainDateTime` and a `ZoneRules`. It assumes `PlainDateTime` is
the local time.
-/
@[inline]
def ofPlainDateTime (pdt : PlainDateTime) (zr : TimeZone.ZoneRules) : ZonedDateTime :=
  let wt := pdt.toWallTime
  let ltt := zr.findLocalTimeTypeForWallTime wt
  let tz := ltt.getTimeZone
  ZonedDateTime.mk (Thunk.mk fun _ => pdt) (wt.toTimestamp tz.offset) zr tz

/--
Creates a new `ZonedDateTime` out of a `Timestamp` and a `TimeZone`.
-/
@[inline]
def ofTimestampWithZone (tm : Timestamp) (tz : TimeZone) : ZonedDateTime :=
  ofTimestamp tm (TimeZone.ZoneRules.ofTimeZone tz)

/--
Creates a new `ZonedDateTime` out of a `PlainDateTime` and a `TimeZone`. It assumes `PlainDateTime` is
the local time.
-/
@[inline]
def ofPlainDateTimeWithZone (tm : PlainDateTime) (tz : TimeZone) : ZonedDateTime :=
  ofPlainDateTime tm (TimeZone.ZoneRules.ofTimeZone tz)

/--
Creates a new `Timestamp` out of a `ZonedDateTime`.
-/
@[inline]
def toTimestamp (date : ZonedDateTime) : Timestamp :=
  date.timestamp

/--
Changes the `ZoneRules` to a new one.
-/
@[inline]
def convertZoneRules (date : ZonedDateTime) (tz₁ : TimeZone.ZoneRules) : ZonedDateTime :=
  ofTimestamp date.toTimestamp tz₁

/--
Converts a `ZonedDateTime` to a `PlainDateTime`
-/
@[inline]
def toPlainDateTime (dt : ZonedDateTime) : PlainDateTime :=
  dt.date.get

/--
Converts a `ZonedDateTime` to a `PlainDateTime`
-/
@[inline]
def toDateTime (dt : ZonedDateTime) : DateTime dt.timezone :=
  DateTime.ofTimestamp dt.timestamp dt.timezone

/--
Getter for the `PlainTime` inside of a `ZonedDateTime`
-/
@[inline]
def time (zdt : ZonedDateTime) : PlainTime :=
  zdt.date.get.time

/--
Getter for the `Year` inside of a `ZonedDateTime`
-/
@[inline]
def year (zdt : ZonedDateTime) : Year.Offset :=
  zdt.date.get.year

/--
Getter for the `Month` inside of a `ZonedDateTime`
-/
@[inline]
def month (zdt : ZonedDateTime) : Month.Ordinal :=
  zdt.date.get.month

/--
Getter for the `Day` inside of a `ZonedDateTime`
-/
@[inline]
def day (zdt : ZonedDateTime) : Day.Ordinal :=
  zdt.date.get.day

/--
Getter for the `Hour` inside of a `ZonedDateTime`
-/
@[inline]
def hour (zdt : ZonedDateTime) : Hour.Ordinal :=
  zdt.date.get.time.hour

/--
Getter for the `Minute` inside of a `ZonedDateTime`
-/
@[inline]
def minute (zdt : ZonedDateTime) : Minute.Ordinal :=
  zdt.date.get.minute

/--
Getter for the `Second` inside of a `ZonedDateTime`
-/
@[inline]
def second (zdt : ZonedDateTime) : Second.Ordinal true :=
  zdt.date.get.time.second

/--
Getter for the `Millisecond` inside of a `ZonedDateTime`.
-/
@[inline]
def millisecond (dt : ZonedDateTime) : Millisecond.Ordinal :=
  dt.date.get.time.millisecond

/--
Getter for the `Nanosecond` inside of a `ZonedDateTime`
-/
@[inline]
def nanosecond (zdt : ZonedDateTime) : Nanosecond.Ordinal :=
  zdt.date.get.time.nanosecond

/--
Getter for the `TimeZone.Offset` inside of a `ZonedDateTime`
-/
@[inline]
def offset (zdt : ZonedDateTime) : TimeZone.Offset :=
  zdt.timezone.offset

/--
Returns the weekday.
-/
@[inline]
def weekday (zdt : ZonedDateTime) : Weekday :=
  zdt.date.get.weekday

/--
Transforms a tuple of a `ZonedDateTime` into a `Day.Ordinal.OfYear`.
-/
@[inline]
def dayOfYear (date : ZonedDateTime) : Day.Ordinal.OfYear date.year.isLeap :=
  ValidDate.dayOfYear ⟨(date.month, date.day), date.date.get.date.valid⟩

/--
Determines the week of the year for the given `ZonedDateTime`, using `firstDay` as the start of the week.
-/
@[inline]
def weekOfYear (date : ZonedDateTime) (firstDay : Weekday := .monday) : Week.Ordinal :=
  date.date.get.weekOfYear firstDay

/--
Returns the week-based year for the given `ZonedDateTime`, using `firstDay` as the start of the week.
The week-based year may differ from the calendar year for dates near the start or end of the year.
-/
@[inline]
def weekYear (date : ZonedDateTime) (firstDay : Weekday := .monday) : Year.Offset :=
  date.date.get.weekYear firstDay

/--
Returns the unaligned week of the month for a `ZonedDateTime` (day divided by 7, plus 1).
-/
def weekOfMonth (date : ZonedDateTime) : Internal.Bounded.LE 1 5 :=
  date.date.get.weekOfMonth

/--
Determines the week of the month for the given `ZonedDateTime`, using `firstDay` as the start of the week.
-/
@[inline]
def alignedWeekOfMonth (date : ZonedDateTime) (firstDay : Weekday := .monday) : Week.Ordinal.OfMonth :=
  date.date.get.alignedWeekOfMonth firstDay

/--
Determines the quarter of the year for the given `ZonedDateTime`.
-/
@[inline]
def quarter (date : ZonedDateTime) : Internal.Bounded.LE 1 4 :=
  date.date.get.quarter

/--
Add `Day.Offset` to a `ZonedDateTime`.
-/
def addDays (dt : ZonedDateTime) (days : Day.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp + days) dt.rules

/--
Subtract `Day.Offset` from a `ZonedDateTime`.
-/
def subDays (dt : ZonedDateTime) (days : Day.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp - days) dt.rules

/--
Add `Week.Offset` to a `ZonedDateTime`.
-/
def addWeeks (dt : ZonedDateTime) (weeks : Week.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp + weeks) dt.rules

/--
Subtract `Week.Offset` from a `ZonedDateTime`.
-/
def subWeeks (dt : ZonedDateTime) (weeks : Week.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp - weeks) dt.rules

/--
Add `Month.Offset` to a `ZonedDateTime`, clipping to the last valid day.
-/
def addMonthsClip (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addMonthsClip months) dt.rules

/--
Subtract `Month.Offset` from a `ZonedDateTime`, clipping to the last valid day.
-/
def subMonthsClip (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subMonthsClip months) dt.rules

/--
Add `Month.Offset` to a `ZonedDateTime`, rolling over excess days.
-/
def addMonthsRollOver (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addMonthsRollOver months) dt.rules

/--
Subtract `Month.Offset` from a `ZonedDateTime`, rolling over excess days.
-/
def subMonthsRollOver (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subMonthsRollOver months) dt.rules

/--
Add `Year.Offset` to a `ZonedDateTime`, rolling over excess days.
-/
def addYearsRollOver (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addYearsRollOver years) dt.rules

/--
Add `Year.Offset` to a `ZonedDateTime`, clipping to the last valid day.
-/
def addYearsClip (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.addYearsClip years) dt.rules

/--
Subtract `Year.Offset` from a `ZonedDateTime`, clipping to the last valid day.
-/
def subYearsClip (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subYearsClip years) dt.rules

/--
Subtract `Year.Offset` from a `ZonedDateTime`, rolling over excess days.
-/
def subYearsRollOver (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  .ofPlainDateTime (dt.toPlainDateTime.subYearsRollOver years) dt.rules

/--
Add `Hour.Offset` to a `ZonedDateTime`.
-/
def addHours (dt : ZonedDateTime) (hours : Hour.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp + hours) dt.rules

/--
Subtract `Hour.Offset` from a `ZonedDateTime`.
-/
def subHours (dt : ZonedDateTime) (hours : Hour.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp - hours) dt.rules
/--
Add `Minute.Offset` to a `ZonedDateTime`.
-/
def addMinutes (dt : ZonedDateTime) (minutes : Minute.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp + minutes) dt.rules

/--
Subtract `Minute.Offset` from a `ZonedDateTime`.
-/
def subMinutes (dt : ZonedDateTime) (minutes : Minute.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp - minutes) dt.rules
/--
Add `Millisecond.Offset` to a `DateTime`.
-/
@[inline]
def addMilliseconds (dt : ZonedDateTime) (milliseconds : Millisecond.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp + milliseconds) dt.rules

/--
Subtract `Millisecond.Offset` from a `DateTime`.
-/
@[inline]
def subMilliseconds (dt : ZonedDateTime) (milliseconds : Millisecond.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp - milliseconds) dt.rules
/--
Add `Second.Offset` to a `ZonedDateTime`.
-/
def addSeconds (dt : ZonedDateTime) (seconds : Second.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp + seconds) dt.rules

/--
Subtract `Second.Offset` from a `ZonedDateTime`.
-/
def subSeconds (dt : ZonedDateTime) (seconds : Second.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp - seconds) dt.rules
/--
Add `Nanosecond.Offset` to a `ZonedDateTime`.
-/
def addNanoseconds (dt : ZonedDateTime) (nanoseconds : Nanosecond.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp + nanoseconds) dt.rules

/--
Subtract `Nanosecond.Offset` from a `ZonedDateTime`.
-/
def subNanoseconds (dt : ZonedDateTime) (nanoseconds : Nanosecond.Offset) : ZonedDateTime :=
  .ofTimestamp (dt.timestamp - nanoseconds) dt.rules
/--
Determines the era of the given `ZonedDateTime` based on its year.
-/
@[inline]
def era (date : ZonedDateTime) : Year.Era :=
  date.date.get.era

/--
Sets the `ZonedDateTime` to the specified `desiredWeekday`.
-/
def withWeekday (dt : ZonedDateTime) (desiredWeekday : Weekday) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withWeekday desiredWeekday) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : ZonedDateTime) (days : Day.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withDaysClip days) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days rolled over to the next month or year as needed.
-/
@[inline]
def withDaysRollOver (dt : ZonedDateTime) (days : Day.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withDaysRollOver days) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the month to the given `month` value.
The day remains unchanged, and any invalid days for the new month will be handled according to the `clip` behavior.
-/
@[inline]
def withMonthClip (dt : ZonedDateTime) (month : Month.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMonthClip month) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : ZonedDateTime) (month : Month.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMonthRollOver month) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the year to the given `year` value. The month and day remain unchanged,
and any invalid days for the new year will be handled according to the `clip` behavior.
-/
@[inline]
def withYearClip (dt : ZonedDateTime) (year : Year.Offset) : ZonedDateTime :=
  let date := dt.date.get

  .ofPlainDateTime (date.withYearClip year) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the year to the given `year` value. The month and day are rolled
over to the next valid month and day if necessary.
-/
@[inline]
def withYearRollOver (dt : ZonedDateTime) (year : Year.Offset) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withYearRollOver year) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `hour` component.
-/
@[inline]
def withHours (dt : ZonedDateTime) (hour : Hour.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withHours hour) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `minute` component.
-/
@[inline]
def withMinutes (dt : ZonedDateTime) (minute : Minute.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMinutes minute) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `second` component.
-/
@[inline]
def withSeconds (dt : ZonedDateTime) (second : Second.Ordinal true) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withSeconds second) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `nano` component with a new `millis` that will set
in the millisecond scale.
-/
@[inline]
def withMilliseconds (dt : ZonedDateTime) (millis : Millisecond.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withMilliseconds millis) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `nano` component.
-/
@[inline]
def withNanoseconds (dt : ZonedDateTime) (nano : Nanosecond.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  .ofPlainDateTime (date.withNanoseconds nano) dt.rules

/--
Checks if the `ZonedDateTime` is in a leap year.
-/
def inLeapYear (date : ZonedDateTime) : Bool :=
  date.year.isLeap

/--
Returns the local (civil) date of the `ZonedDateTime` as a `Day.Offset` relative to 1970-01-01.
-/
def toEpochDay (date : ZonedDateTime) : Day.Offset :=
  date.date.get.toEpochDay

/--
Creates a `ZonedDateTime` from a local date given as a `Day.Offset` relative to 1970-01-01, a
`PlainTime`, and `ZoneRules`. The day offset is interpreted as a local (civil) date, not UTC.
-/
@[inline]
def ofEpochDay (days : Day.Offset) (time : PlainTime) (zt : TimeZone.ZoneRules) : ZonedDateTime :=
  ZonedDateTime.ofPlainDateTime (PlainDateTime.ofEpochDay days time) zt

instance : HAdd ZonedDateTime Day.Offset ZonedDateTime where
  hAdd := addDays

instance : HSub ZonedDateTime Day.Offset ZonedDateTime where
  hSub := subDays

instance : HAdd ZonedDateTime Week.Offset ZonedDateTime where
  hAdd := addWeeks

instance : HSub ZonedDateTime Week.Offset ZonedDateTime where
  hSub := subWeeks

instance : HAdd ZonedDateTime Hour.Offset ZonedDateTime where
  hAdd := addHours

instance : HSub ZonedDateTime Hour.Offset ZonedDateTime where
  hSub := subHours

instance : HAdd ZonedDateTime Minute.Offset ZonedDateTime where
  hAdd := addMinutes

instance : HSub ZonedDateTime Minute.Offset ZonedDateTime where
  hSub := subMinutes

instance : HAdd ZonedDateTime Second.Offset ZonedDateTime where
  hAdd := addSeconds

instance : HSub ZonedDateTime Second.Offset ZonedDateTime where
  hSub := subSeconds

instance : HAdd ZonedDateTime Millisecond.Offset ZonedDateTime where
  hAdd := addMilliseconds

instance : HSub ZonedDateTime Millisecond.Offset ZonedDateTime where
  hSub := subMilliseconds

instance : HAdd ZonedDateTime Nanosecond.Offset ZonedDateTime where
  hAdd := addNanoseconds

instance : HSub ZonedDateTime Nanosecond.Offset ZonedDateTime where
  hSub := subNanoseconds

instance : HSub ZonedDateTime ZonedDateTime Duration where
  hSub x y := x.toTimestamp - y.toTimestamp

instance : HAdd ZonedDateTime Duration ZonedDateTime where
  hAdd x y := x.addNanoseconds y.toNanoseconds

instance : HSub ZonedDateTime Duration ZonedDateTime where
  hSub x y := x.subNanoseconds y.toNanoseconds

end ZonedDateTime
end Time
end Std
