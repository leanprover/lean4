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
An existential version of `DateTime` that encapsulates a `DateTime` value without explicitly storing
the time zone.
-/
def ZonedDateTime := Sigma DateTime

instance : BEq ZonedDateTime where
  beq x y := x.fst == y.fst && x.snd.timestamp == y.snd.timestamp

instance : CoeDep ZonedDateTime d (DateTime d.fst) where
  coe := d.snd

instance : Inhabited ZonedDateTime where
  default := ⟨Inhabited.default, Inhabited.default⟩

namespace ZonedDateTime
open DateTime

/--
Creates a new `ZonedDateTime` out of a `DateTime` and `TimeZone`
-/
@[inline]
def mk (tz : TimeZone) (datetime : DateTime tz) : ZonedDateTime :=
  ⟨tz, datetime⟩

/--
Creates a new `ZonedDateTime` out of a `Timestamp`
-/
@[inline]
def ofTimestamp (tm : Timestamp) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofTimestamp tm tz⟩

/--
Creates a new `Timestamp` out of a `ZonedDateTime`
-/
@[inline]
def toTimestamp (date : ZonedDateTime) : Timestamp :=
  date.snd.toTimestamp

/--
Creates a new `ZonedDateTime` out of a `Timestamp`
-/
@[inline]
def ofZoneRules (tm : Timestamp) (rules : TimeZone.ZoneRules) : Option ZonedDateTime := do
  let transition ← rules.findTransitionForTimestamp tm
  let tm := rules.applyLeapSeconds tm
  return ofTimestamp tm transition.localTimeType.getTimeZone

/--
Changes the `TimeZone` to a new one.
-/
@[inline]
def convertTimeZone (date : ZonedDateTime) (tz₁ : TimeZone) : ZonedDateTime :=
  ofTimestamp date.toTimestamp tz₁

/--
Creates a new `ZonedDateTime` out of a `PlainDateTime`
-/
@[inline]
def ofPlainDateTimeAssumingUTC (date : PlainDateTime) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofPlainDateTimeAssumingUTC date tz⟩

/--
Converts a `ZonedDateTime` to a `PlainDateTime`
-/
@[inline]
def toPlainDateTime (dt : ZonedDateTime) : PlainDateTime :=
  DateTime.toPlainDateTime dt.snd

/--
Getter for the `Year` inside of a `ZonedDateTime`
-/
@[inline]
def year (zdt : ZonedDateTime) : Year.Offset :=
  zdt.snd.year

/--
Getter for the `Month` inside of a `ZonedDateTime`
-/
@[inline]
def month (zdt : ZonedDateTime) : Month.Ordinal :=
  zdt.snd.month

/--
Getter for the `Day` inside of a `ZonedDateTime`
-/
@[inline]
def day (zdt : ZonedDateTime) : Day.Ordinal :=
  zdt.snd.day

/--
Getter for the `Hour` inside of a `ZonedDateTime`
-/
@[inline]
def hour (zdt : ZonedDateTime) : Hour.Ordinal :=
  zdt.snd.date.get.time.hour

/--
Getter for the `Minute` inside of a `ZonedDateTime`
-/
@[inline]
def minute (zdt : ZonedDateTime) : Minute.Ordinal :=
  zdt.snd.minute

/--
Getter for the `Second` inside of a `ZonedDateTime`
-/
@[inline]
def second (zdt : ZonedDateTime) : Second.Ordinal zdt.snd.date.get.time.second.fst :=
  zdt.snd.date.get.time.second.snd

/--
Getter for the `Nanosecond` inside of a `ZonedDateTime`
-/
@[inline]
def nano (zdt : ZonedDateTime) : Nanosecond.Ordinal :=
  zdt.snd.date.get.time.nano

/--
Getter for the `TimeZone.Offset` inside of a `ZonedDateTime`
-/
@[inline]
def offset (zdt : ZonedDateTime) : TimeZone.Offset :=
  zdt.fst.offset

/--
Getter for the `TimeZone.Offset` inside of a `ZonedDateTime`
-/
@[inline]
def timezone (zdt : ZonedDateTime) : TimeZone :=
  zdt.fst

/--
Returns the weekday.
-/
@[inline]
def weekday (zdt : ZonedDateTime) : Weekday :=
  zdt.snd.weekday

/--
Add `Day.Offset` to a `ZonedDateTime`.
-/
def addDays (dt : ZonedDateTime) (days : Day.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addDays days)

/--
Subtracts `Day.Offset` to a `ZonedDateTime`.
-/
@[inline]
def subDays (dt : ZonedDateTime) (days : Day.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subDays days)

/--
Add `Week.Offset` to a `ZonedDateTime`.
-/
def addWeeks (dt : ZonedDateTime) (weeks : Week.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addWeeks weeks)

/--
Subtracts `Week.Offset` to a `ZonedDateTime`.
-/
@[inline]
def subWeeks (dt : ZonedDateTime) (weeks : Week.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subWeeks weeks)

/--
Add `Month.Offset` to a `ZonedDateTime`, it clips the day to the last valid day of that month.
-/
def addMonthsClip (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addMonthsClip months)

/--
Subtracts `Month.Offset` to a `ZonedDateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subMonthsClip months)

/--
Add `Month.Offset` to a `ZonedDateTime`, this function rolls over any excess days into the following
month.
-/
def addMonthsRollOver (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addMonthsRollOver months)

/--
Add `Month.Offset` to a `ZonedDateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def subMonthsRollOver (dt : ZonedDateTime) (months : Month.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subMonthsRollOver months)

/--
Add `Year.Offset` to a `ZonedDateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def addYearsRollOver (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addYearsRollOver years)

/--
Add `Year.Offset` to a `ZonedDateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def addYearsClip (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addYearsClip years)

/--
Subtract `Year.Offset` from a `ZonedDateTime`, this function clips the day to the last valid day of that month.
-/
@[inline]
def subYearsClip (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subYearsClip years)

/--
Subtract `Year.Offset` from a `ZonedDateTime`, this function rolls over any excess days into the previous month.
-/
@[inline]
def subYearsRollOver (dt : ZonedDateTime) (years : Year.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subYearsRollOver years)

/--
Add `Hour.Offset` to a `ZonedDateTime`, adjusting the date if necessary.
-/
def addHours (dt : ZonedDateTime) (hours : Hour.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addHours hours)

/--
Subtract `Hour.Offset` from a `ZonedDateTime`, adjusting the date if necessary.
-/
@[inline]
def subHours (dt : ZonedDateTime) (hours : Hour.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subHours hours)

/--
Add `Minute.Offset` to a `ZonedDateTime`, adjusting the date if necessary.
-/
def addMinutes (dt : ZonedDateTime) (minutes : Minute.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addMinutes minutes)

/--
Subtract `Minute.Offset` from a `ZonedDateTime`, adjusting the date if necessary.
-/
@[inline]
def subMinutes (dt : ZonedDateTime) (minutes : Minute.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subMinutes minutes)

/--
Add `Second.Offset` to a `ZonedDateTime`, adjusting the date if necessary.
-/
def addSeconds (dt : ZonedDateTime) (seconds : Second.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addSeconds seconds)

/--
Subtract `Second.Offset` from a `ZonedDateTime`, adjusting the date if necessary.
-/
@[inline]
def subSeconds (dt : ZonedDateTime) (seconds : Second.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subSeconds seconds)

/--
Add `Nanosecond.Offset` to a `ZonedDateTime`, adjusting the date if necessary.
-/
def addNanoseconds (dt : ZonedDateTime) (nanoseconds : Nanosecond.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.addNanoseconds nanoseconds)

/--
Subtract `Nanosecond.Offset` from a `ZonedDateTime`, adjusting the date if necessary.
-/
@[inline]
def subNanoseconds (dt : ZonedDateTime) (nanoseconds : Nanosecond.Offset) : ZonedDateTime :=
  Sigma.mk dt.fst (dt.snd.subNanoseconds nanoseconds)

/--
Determines the era of the given `PlainDate` based on its year.
-/
@[inline]
def era (date : ZonedDateTime) : Year.Era :=
  if date.year.toInt ≥ 0 then
    .ce
  else
    .bce

/--
Creates a new `ZonedDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : ZonedDateTime) (days : Day.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withDaysClip days⟩

/--
Creates a new `ZonedDateTime` by adjusting the day of the month to the given `days` value, with any
out-of-range days rolled over to the next month or year as needed.
-/
@[inline]
def withDaysRollOver (dt : ZonedDateTime) (days : Day.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withDaysRollOver days⟩

/--
Creates a new `ZonedDateTime` by adjusting the month to the given `month` value.
The day remains unchanged, and any invalid days for the new month will be handled according to the `clip` behavior.
-/
@[inline]
def withMonthClip (dt : ZonedDateTime) (month : Month.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withMonthClip month⟩

/--
Creates a new `ZonedDateTime` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : ZonedDateTime) (month : Month.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withMonthRollOver month⟩

/--
Creates a new `ZonedDateTime` by adjusting the year to the given `year` value. The month and day remain unchanged,
and any invalid days for the new year will be handled according to the `clip` behavior.
-/
@[inline]
def withYearClip (dt : ZonedDateTime) (year : Year.Offset) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withYearClip year⟩

/--
Creates a new `ZonedDateTime` by adjusting the year to the given `year` value. The month and day are rolled
over to the next valid month and day if necessary.
-/
@[inline]
def withYearRollOver (dt : ZonedDateTime) (year : Year.Offset) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withYearRollOver year⟩

/--
Creates a new `ZonedDateTime` by adjusting the `hour` component.
-/
@[inline]
def withHour (dt : ZonedDateTime) (hour : Hour.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withHour hour⟩

/--
Creates a new `ZonedDateTime` by adjusting the `minute` component.
-/
@[inline]
def withMinute (dt : ZonedDateTime) (minute : Minute.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withMinute minute⟩

/--
Creates a new `ZonedDateTime` by adjusting the `second` component.
-/
@[inline]
def withSecond (dt : ZonedDateTime) (second : Sigma Second.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withSecond second⟩

/--
Creates a new `ZonedDateTime` by adjusting the `nano` component.
-/
@[inline]
def withNano (dt : ZonedDateTime) (nano : Nanosecond.Ordinal) : ZonedDateTime :=
  ⟨dt.fst, dt.snd.withNano nano⟩

/--
Checks if the `DateTime` is in a leap year.
-/
def inLeapYear (date : ZonedDateTime) : Bool :=
  date.year.isLeap

instance : ToTimestamp ZonedDateTime where
  toTimestamp dt := dt.toTimestamp

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
