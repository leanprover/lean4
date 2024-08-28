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

set_option linter.all true

/--
It stores a `Timestamp`, a `PlainDateTime` and a `TimeZone`
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

instance : Inhabited (DateTime tz) where
  default := ⟨Inhabited.default, Thunk.mk λ_ => Inhabited.default⟩

namespace DateTime

/--
Creates a new `DateTime` out of a `Timestamp` that is in a `TimeZone`.
-/
@[inline]
def ofTimestamp (tm : Timestamp) (tz : TimeZone) : DateTime tz :=
  DateTime.mk tm (Thunk.mk <| λ_ => (tm.addSeconds tz.toSeconds).toPlainDateTime)

/--
Creates a new zone aware `Timestamp` out of a `DateTime`.
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
Creates a new `DateTime` out of a `PlainDateTime`
-/
@[inline]
def ofPlainDateTime (date : PlainDateTime) (tz : TimeZone) : DateTime tz :=
  let tm := Timestamp.ofPlainDateTime date
  DateTime.mk (tm.subSeconds tz.toSeconds) (Thunk.mk <| λ_ => date)

/--
Add `Hour.Offset` to a `DateTime`.
-/
@[inline]
def addHours (dt : DateTime tz) (hours : Hour.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addHours hours) tz

/--
Subtract `Hour.Offset` from a `DateTime`.
-/
@[inline]
def subHours (dt : DateTime tz) (hours : Hour.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subHours hours) tz

/--
Add `Minute.Offset` to a `DateTime`.
-/
@[inline]
def addMinutes (dt : DateTime tz) (minutes : Minute.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addMinutes minutes) tz

/--
Subtract `Minute.Offset` from a `DateTime`.
-/
@[inline]
def subMinutes (dt : DateTime tz) (minutes : Minute.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subMinutes minutes) tz

/--
Add `Second.Offset` to a `DateTime`.
-/
@[inline]
def addSeconds (dt : DateTime tz) (seconds : Second.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addSeconds seconds) tz

/--
Subtract `Second.Offset` from a `DateTime`.
-/
@[inline]
def subSeconds (dt : DateTime tz) (seconds : Second.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subSeconds seconds) tz

/--
Add `Nanosecond.Offset` to a `DateTime`.
-/
@[inline]
def addNanoseconds (dt : DateTime tz) (nanoseconds : Nanosecond.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addNanoseconds nanoseconds) tz

/--
Subtract `Nanosecond.Offset` from a `DateTime`.
-/
@[inline]
def subNanoseconds (dt : DateTime tz) (nanoseconds : Nanosecond.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subNanoseconds nanoseconds) tz

/--
Add `Day.Offset` to a `DateTime`.
-/
@[inline]
def addDays (dt : DateTime tz) (days : Day.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addDays days) tz

/--
Subtracts `Day.Offset` to a `DateTime`.
-/
@[inline]
def subDays (dt : DateTime tz) (days : Day.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subDays days) tz

/--
Add `Month.Offset` to a `DateTime`, it clips the day to the last valid day of that month.
-/
def addMonthsClip (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addMonthsClip months) tz

/--
Subtracts `Month.Offset` from a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subMonthsClip months) tz

/--
Add `Month.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
def addMonthsRollOver (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addMonthsRollOver months) tz

/--
Subtract `Month.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def subMonthsRollOver (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subMonthsRollOver months) tz

/--
Add `Year.Offset` to a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def addYearsRollOver (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addYearsRollOver years) tz

/--
Add `Year.Offset` to a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def addYearsClip (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.addYearsClip years) tz

/--
Subtract `Year.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def subYearsRollOver (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subYearsRollOver years) tz

/--
Subtract `Year.Offset` from to a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subYearsClip (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofPlainDateTime (dt.timestamp.toPlainDateTime.subYearsClip years) tz

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
def hour (dt : DateTime tz) : Hour.Ordinal dt.date.get.time.hour.fst :=
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
def second (dt : DateTime tz) : Second.Ordinal dt.date.get.time.second.fst :=
  dt.date.get.second

/--
Getter for the `Milliseconds` inside of a `DateTime`
-/
@[inline]
def milliseconds (dt : DateTime tz) : Millisecond.Ordinal :=
  dt.date.get.time.nano.toMillisecond

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
  if date.year.toInt ≥ 0 then
    .ce
  else
    .bce

/--
Checks if the `DateTime` is in a leap year.
-/
def inLeapYear (date : DateTime tz) : Bool :=
  date.year.isLeap

instance : ToTimestamp (DateTime tz) where
  toTimestamp dt := dt.toTimestamp

instance : HAdd (DateTime tz) (Day.Offset) (DateTime tz) where
  hAdd := addDays

instance : HSub (DateTime tz) (Day.Offset) (DateTime tz) where
  hSub := subDays

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

instance : HAdd (DateTime tz) (Nanosecond.Offset) (DateTime tz) where
  hAdd := addNanoseconds

instance : HSub (DateTime tz) (Nanosecond.Offset) (DateTime tz) where
  hSub := subNanoseconds

end DateTime
end Time
end Std
