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
It stores a `Timestamp`, a `LocalDateTime` and a `TimeZone`
-/
structure DateTime (tz : TimeZone) where
  private mk ::

  /--
  `Timestamp` represents the exact moment in time. It's a UTC related `Timestamp`.
  -/
  timestamp : Timestamp

  /--
  `Date` is a `Thunk` containing the `LocalDateTime` that represents the local date and time, it's
  used for accessing data like `day` and `month` without having to recompute the data everytime.
  -/
  date : Thunk LocalDateTime

instance : BEq (DateTime tz) where
  beq x y := x.timestamp == y.timestamp

instance : Inhabited (DateTime tz) where
  default := ⟨Inhabited.default, Thunk.mk λ_ => Inhabited.default⟩

namespace DateTime

/--
Creates a new `DateTime` out of a `Timestamp` that is in a `TimeZone`.
-/
@[inline]
def ofUTCTimestamp (tm : Timestamp) (tz : TimeZone) : DateTime tz :=
  DateTime.mk tm (Thunk.mk <| λ_ => (tm.addSeconds tz.toSeconds).toLocalDateTime)

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
  ofUTCTimestamp date.timestamp tz₁


/--
Creates a new `DateTime` out of a `LocalDateTime`
-/
@[inline]
def ofLocalDateTime (date : LocalDateTime) (tz : TimeZone) : DateTime tz :=
  let tm := Timestamp.ofLocalDateTime date
  DateTime.mk (tm.subSeconds tz.toSeconds) (Thunk.mk <| λ_ => date)

/--
Gets the current `DateTime`.
-/
@[inline]
def now : IO (DateTime tz) := do
  let loca ← LocalDateTime.now
  return ofLocalDateTime loca tz

/--
Add `Day.Offset` to a `DateTime`.
-/
@[inline]
def addDays (dt : DateTime tz) (days : Day.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.addDays days) tz

/--
Subtracts `Day.Offset` to a `DateTime`.
-/
@[inline]
def subDays (dt : DateTime tz) (days : Day.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.subDays days) tz

/--
Add `Month.Offset` to a `DateTime`, it clips the day to the last valid day of that month.
-/
def addMonthsClip (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.addMonthsClip months) tz

/--
Subtracts `Month.Offset` from a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.subMonthsClip months) tz

/--
Add `Month.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
def addMonthsRollOver (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.addMonthsRollOver months) tz

/--
Subtract `Month.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def subMonthsRollOver (dt : DateTime tz) (months : Month.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.subMonthsRollOver months) tz

/--
Add `Year.Offset` to a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def addYearsRollOver (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.addYearsRollOver years) tz

/--
Add `Year.Offset` to a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def addYearsClip (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.addYearsClip years) tz

/--
Subtract `Year.Offset` from a `DateTime`, this function rolls over any excess days into the following
month.
-/
@[inline]
def subYearsRollOver (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.subYearsRollOver years) tz

/--
Subtract `Year.Offset` from to a `DateTime`, it clips the day to the last valid day of that month.
-/
@[inline]
def subYearsClip (dt : DateTime tz) (years : Year.Offset) : DateTime tz :=
  ofLocalDateTime (dt.timestamp.toLocalDateTime.subYearsClip years) tz

/--
Converts a `Timestamp` to a `LocalDateTime`
-/
@[inline]
def toLocalDateTime (dt : DateTime tz) : LocalDateTime :=
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

end DateTime
end Time
end Std
