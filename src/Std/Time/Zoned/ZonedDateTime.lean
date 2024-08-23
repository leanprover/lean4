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
Creates a new `DateTime` out of a `Timestamp`
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
  ofTimestamp (date.toTimestamp) tz₁

/--
Creates a new `ZonedDateTime` out of a `LocalDateTime`
-/
@[inline]
def ofLocalDateTime (date : LocalDateTime) (tz : TimeZone) : ZonedDateTime :=
  ⟨tz, DateTime.ofLocalDateTime date tz⟩

/--
Converts a `ZonedDateTime` to a `LocalDateTime`
-/
@[inline]
def toLocalDateTime (dt : ZonedDateTime) : LocalDateTime :=
  DateTime.toLocalDateTime dt.snd

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
def hour (zdt : ZonedDateTime) : Hour.Ordinal zdt.snd.date.get.time.hour.fst :=
  zdt.snd.date.get.time.hour.snd

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

instance : HAdd ZonedDateTime (Day.Offset) ZonedDateTime where
  hAdd := addDays

instance : HSub ZonedDateTime (Day.Offset) ZonedDateTime where
  hSub := subDays

instance : HAdd ZonedDateTime (Hour.Offset) ZonedDateTime where
  hAdd := addHours

instance : HSub ZonedDateTime (Hour.Offset) ZonedDateTime where
  hSub := subHours

instance : HAdd ZonedDateTime (Minute.Offset) ZonedDateTime where
  hAdd := addMinutes

instance : HSub ZonedDateTime (Minute.Offset) ZonedDateTime where
  hSub := subMinutes

instance : HAdd ZonedDateTime (Second.Offset) ZonedDateTime where
  hAdd := addSeconds

instance : HSub ZonedDateTime (Second.Offset) ZonedDateTime where
  hSub := subSeconds

end ZonedDateTime
end Time
end Std
