/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Zoned.DateTime
import Std.Time.Zoned.ZoneRules

namespace Std
namespace Time

set_option linter.all true

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
  default := ⟨Thunk.mk Inhabited.default, Inhabited.default, Inhabited.default, Inhabited.default⟩

namespace ZonedDateTime
open DateTime

/--
Creates a new `ZonedDateTime` out of a `Timestamp` and a `ZoneRules`.
-/
@[inline]
def ofTimestamp (tm : Timestamp) (rules : TimeZone.ZoneRules) : ZonedDateTime :=
  let tz := rules.timezoneAt tm
  ZonedDateTime.mk (Thunk.mk fun _ => (tm.addSeconds tz.toSeconds) |>.toPlainDateTimeAssumingUTC) tm rules tz

/--
Creates a new `ZonedDateTime` out of a `PlainDateTime` and a `ZoneRules`.
-/
@[inline]
def ofPlainDateTime (pdt : PlainDateTime) (zr : TimeZone.ZoneRules) : ZonedDateTime :=
  let tm := pdt.toTimestampAssumingUTC
  let tz := zr.findLocalTimeTypeForTimestamp tm |>.getTimeZone
  let tm := tm.subSeconds tz.toSeconds
  ZonedDateTime.mk (Thunk.mk fun _ => (tm.addSeconds tz.toSeconds) |>.toPlainDateTimeAssumingUTC) tm zr tz

/--
Creates a new `Timestamp` out of a `ZonedDateTime`.
-/
@[inline]
def toTimestamp (date : ZonedDateTime) : Timestamp :=
  date.timestamp

/--
Changes the `ZoleRules` to a new one.
-/
@[inline]
def convertZoneRules (date : ZonedDateTime) (tz₁ : TimeZone.ZoneRules) : ZonedDateTime :=
  ofTimestamp date.toTimestamp tz₁

/--
Creates a new `ZonedDateTime` out of a `PlainDateTime`
-/
@[inline]
def ofPlainDateTimeAssumingUTC (date : PlainDateTime) (tz : TimeZone.ZoneRules) : ZonedDateTime :=
  ofTimestamp date.toTimestampAssumingUTC tz

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
def second (zdt : ZonedDateTime) : Second.Ordinal zdt.date.get.time.second.fst :=
  zdt.date.get.time.second.snd

/--
Getter for the `Nanosecond` inside of a `ZonedDateTime`
-/
@[inline]
def nanosecond (zdt : ZonedDateTime) : Nanosecond.Ordinal :=
  zdt.date.get.time.nano

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
def toOrdinal (date : ZonedDateTime) : Day.Ordinal.OfYear date.year.isLeap :=
  ValidDate.toOrdinal ⟨(date.month, date.day), date.date.get.date.valid⟩

/--
Add `Day.Offset` to a `ZonedDateTime`.
-/
def addDays (dt : ZonedDateTime) (days : Day.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addDays days).toTimestampAssumingUTC dt.rules

/--
Subtract `Day.Offset` from a `ZonedDateTime`.
-/
def subDays (dt : ZonedDateTime) (days : Day.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subDays days).toTimestampAssumingUTC dt.rules

/--
Add `Week.Offset` to a `ZonedDateTime`.
-/
def addWeeks (dt : ZonedDateTime) (weeks : Week.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addWeeks weeks).toTimestampAssumingUTC dt.rules

/--
Subtract `Week.Offset` from a `ZonedDateTime`.
-/
def subWeeks (dt : ZonedDateTime) (weeks : Week.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subWeeks weeks).toTimestampAssumingUTC dt.rules

/--
Add `Month.Offset` to a `ZonedDateTime`, clipping to the last valid day.
-/
def addMonthsClip (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addMonthsClip months).toTimestampAssumingUTC dt.rules

/--
Subtract `Month.Offset` from a `ZonedDateTime`, clipping to the last valid day.
-/
def subMonthsClip (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subMonthsClip months).toTimestampAssumingUTC dt.rules

/--
Add `Month.Offset` to a `ZonedDateTime`, rolling over excess days.
-/
def addMonthsRollOver (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addMonthsRollOver months).toTimestampAssumingUTC dt.rules

/--
Subtract `Month.Offset` from a `ZonedDateTime`, rolling over excess days.
-/
def subMonthsRollOver (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subMonthsRollOver months).toTimestampAssumingUTC dt.rules

/--
Add `Year.Offset` to a `ZonedDateTime`, rolling over excess days.
-/
def addYearsRollOver (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addYearsRollOver years).toTimestampAssumingUTC dt.rules

/--
Add `Year.Offset` to a `ZonedDateTime`, clipping to the last valid day.
-/
def addYearsClip (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addYearsClip years).toTimestampAssumingUTC dt.rules

/--
Subtract `Year.Offset` from a `ZonedDateTime`, clipping to the last valid day.
-/
def subYearsClip (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subYearsClip years).toTimestampAssumingUTC dt.rules

/--
Subtract `Year.Offset` from a `ZonedDateTime`, rolling over excess days.
-/
def subYearsRollOver (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subYearsRollOver years).toTimestampAssumingUTC dt.rules

/--
Add `Hour.Offset` to a `ZonedDateTime`.
-/
def addHours (dt : ZonedDateTime) (hours : Hour.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addHours hours).toTimestampAssumingUTC dt.rules

/--
Subtract `Hour.Offset` from a `ZonedDateTime`.
-/
def subHours (dt : ZonedDateTime) (hours : Hour.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subHours hours).toTimestampAssumingUTC dt.rules

/--
Add `Minute.Offset` to a `ZonedDateTime`.
-/
def addMinutes (dt : ZonedDateTime) (minutes : Minute.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addMinutes minutes).toTimestampAssumingUTC dt.rules

/--
Subtract `Minute.Offset` from a `ZonedDateTime`.
-/
def subMinutes (dt : ZonedDateTime) (minutes : Minute.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subMinutes minutes).toTimestampAssumingUTC dt.rules

/--
Add `Second.Offset` to a `ZonedDateTime`.
-/
def addSeconds (dt : ZonedDateTime) (seconds : Second.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addSeconds seconds).toTimestampAssumingUTC dt.rules

/--
Subtract `Second.Offset` from a `ZonedDateTime`.
-/
def subSeconds (dt : ZonedDateTime) (seconds : Second.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subSeconds seconds).toTimestampAssumingUTC dt.rules

/--
Add `Nanosecond.Offset` to a `ZonedDateTime`.
-/
def addNanoseconds (dt : ZonedDateTime) (nanoseconds : Nanosecond.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.addNanoseconds nanoseconds).toTimestampAssumingUTC dt.rules

/--
Subtract `Nanosecond.Offset` from a `ZonedDateTime`.
-/
def subNanoseconds (dt : ZonedDateTime) (nanoseconds : Nanosecond.Offset) : ZonedDateTime :=
  let date := dt.timestamp.toPlainDateTimeAssumingUTC
  ZonedDateTime.ofTimestamp (date.subNanoseconds nanoseconds).toTimestampAssumingUTC dt.rules

/--
Determines the era of the given `ZonedDateTime` based on its year.
-/
@[inline]
def era (date : ZonedDateTime) : Year.Era :=
  date.date.get.era

/--
Creates a new `ZonedDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : ZonedDateTime) (days : Day.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withDaysClip days) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days rolled over to the next month or year as needed.
-/
@[inline]
def withDaysRollOver (dt : ZonedDateTime) (days : Day.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withDaysRollOver days) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the month to the given `month` value.
The day remains unchanged, and any invalid days for the new month will be handled according to the `clip` behavior.
-/
@[inline]
def withMonthClip (dt : ZonedDateTime) (month : Month.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withMonthClip month) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : ZonedDateTime) (month : Month.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withMonthRollOver month) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the year to the given `year` value. The month and day remain unchanged,
and any invalid days for the new year will be handled according to the `clip` behavior.
-/
@[inline]
def withYearClip (dt : ZonedDateTime) (year : Year.Offset) : ZonedDateTime :=
  let date := dt.date.get

  ZonedDateTime.ofPlainDateTime (date.withYearClip year) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the year to the given `year` value. The month and day are rolled
over to the next valid month and day if necessary.
-/
@[inline]
def withYearRollOver (dt : ZonedDateTime) (year : Year.Offset) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withYearRollOver year) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `hour` component.
-/
@[inline]
def withHours (dt : ZonedDateTime) (hour : Hour.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withHours hour) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `minute` component.
-/
@[inline]
def withMinutes (dt : ZonedDateTime) (minute : Minute.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withMinutes minute) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `second` component.
-/
@[inline]
def withSeconds (dt : ZonedDateTime) (second : Sigma Second.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withSeconds second) dt.rules

/--
Creates a new `ZonedDateTime` by adjusting the `nano` component.
-/
@[inline]
def withNanoseconds (dt : ZonedDateTime) (nano : Nanosecond.Ordinal) : ZonedDateTime :=
  let date := dt.date.get
  ZonedDateTime.ofPlainDateTime (date.withNanoseconds nano) dt.rules

/--
Checks if the `ZonedDateTime` is in a leap year.
-/
def inLeapYear (date : ZonedDateTime) : Bool :=
  date.year.isLeap

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

instance : HAdd ZonedDateTime Nanosecond.Offset ZonedDateTime where
  hAdd := addNanoseconds

instance : HSub ZonedDateTime Nanosecond.Offset ZonedDateTime where
  hSub := subNanoseconds

instance : HSub ZonedDateTime ZonedDateTime Duration where
  hSub x y := x.toTimestamp - y.toTimestamp

end ZonedDateTime
end Time
end Std
