/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Std.Time.Date.Basic
import Std.Internal.Rat

namespace Std
namespace Time
open Std.Internal
open Internal
open Lean

set_option linter.all true

/--
`PlainDate` represents a date in the Year-Month-Day (YMD) format. It encapsulates the year, month,
and day components, with validation to ensure the date is valid.
-/
structure PlainDate where

  /-- The year component of the date. It is represented as an `Offset` type from `Year`. -/
  year : Year.Offset

  /-- The month component of the date. It is represented as an `Ordinal` type from `Month`. -/
  month : Month.Ordinal

  /-- The day component of the date. It is represented as an `Ordinal` type from `Day`. -/
  day : Day.Ordinal

  /-- Validates the date by ensuring that the year, month, and day form a correct and valid date. -/
  valid : year.Valid month day


instance : BEq PlainDate where
  beq x y := x.day == y.day && x.month == y.month && x.year == y.year

namespace PlainDate

/--
Creates a `PlainDate` by clipping the day to ensure validity. This function forces the date to be
valid by adjusting the day to fit within the valid range to fit the given month and year.
-/
@[inline]
def clip (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : PlainDate :=
  let day := month.clipDay year.isLeap day
  PlainDate.mk year month day Month.Ordinal.clipDay_valid

instance : Inhabited PlainDate where
  default := mk 0 1 1 (by decide)

/--
Creates a new `PlainDate` from year, month, and day components.
-/
@[inline]
def ofYearMonthDay (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Option PlainDate :=
  if valid : year.Valid month day
    then some (PlainDate.mk year month day valid)
    else none

/--
Creates a `PlainDate` from a year and a day ordinal within that year.
-/
@[inline]
def ofYearOrdinal (year : Year.Offset) (ordinal : Day.Ordinal.OfYear year.isLeap) : PlainDate :=
  let ⟨⟨month, day⟩, proof⟩ := Month.Ordinal.ofOrdinal ordinal
  ⟨year, month, day, proof⟩

/--
Creates a `PlainDate` from the number of days since the UNIX epoch (January 1st, 1970).
-/
def ofDaysSinceUNIXEpoch (day : Day.Offset) : PlainDate :=
  let z := day.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096).tdiv 146097
  let doe := z - era * 146097
  let yoe := (doe - doe.tdiv 1460 + doe.tdiv 36524 - doe.tdiv 146096).tdiv 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe.tdiv 4 - yoe.tdiv 100)
  let mp := (5 * doy + 2).tdiv 153
  let d := doy - (153 * mp + 2).tdiv 5 + 1
  let m := mp + (if mp < 10 then 3 else -9)
  let y := y + (if m <= 2 then 1 else 0)
  .clip y (.clip m (by decide)) (.clip d (by decide))

/--
Calculates the `Weekday` of a given `PlainDate` using Zeller's Congruence for the Gregorian calendar.
-/
def weekday (date : PlainDate) : Weekday :=
  let q := date.day
  let m := date.month
  let y := date.year.toInt

  let y := if m.val < 2 then y - 1 else y

  let m : Bounded.LE 1 13 := if h : m.val ≤ 1
    then (m.truncateTop h |>.add 12 |>.expandBottom (by decide))
    else m.expandTop (by decide)

  let k := Bounded.LE.byEmod y 100 (by decide)
  let j : Bounded.LE (-10) 9 := (Bounded.LE.byMod y 1000 (by decide)).ediv 100 (by decide)
  let part : Bounded.LE 6 190 := q.addBounds (((m.add 1).mul_pos 13 (by decide)).ediv 5 (by decide)) |>.addBounds k |>.addBounds (k.ediv 4 (by decide))
  let h : Bounded.LE (-15) 212 := part.addBounds ((j.ediv 4 (by decide)).addBounds (j.mul_pos 2 (by decide)).neg)
  let d :=  (h.add 6).emod 7 (by decide)

  .ofOrdinal (d.add 1)

/--
Determines the era of the given `PlainDate` based on its year.
-/
def era (date : PlainDate) : Year.Era :=
  if date.year.toInt ≥ 0 then
    .ce
  else
    .bce

/--
Checks if the `PlainDate` is in a leap year.
-/
@[inline]
def inLeapYear (date : PlainDate) : Bool :=
  date.year.isLeap

/--
Converts a `PlainDate` to the number of days since the UNIX epoch.
-/
def toDaysSinceUNIXEpoch (date : PlainDate) : Day.Offset :=
  let y : Int := if date.month.toInt > 2 then date.year else date.year.toInt - 1
  let era : Int := (if y ≥ 0 then y else y - 399).tdiv 400
  let yoe : Int := y - era * 400
  let m : Int := date.month.toInt
  let d : Int := date.day.toInt
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2).tdiv 5 + d - 1
  let doe := yoe * 365 + yoe.tdiv 4 - yoe.tdiv 100 + doy

  .ofInt (era * 146097 + doe - 719468)

/--
Calculates the difference in years between a `PlainDate` and a given year.
-/
@[inline]
def yearsSince (date : PlainDate) (year : Year.Offset) : Year.Offset :=
  date.year - year

/--
Adds a given number of days to a `PlainDate`.
-/
@[inline]
def addDays (date : PlainDate) (days : Day.Offset) : PlainDate :=
  let dateDays := date.toDaysSinceUNIXEpoch
  ofDaysSinceUNIXEpoch (dateDays + days)

/--
Subtracts a given number of days from a `PlainDate`.
-/
@[inline]
def subDays (date : PlainDate) (days : Day.Offset) : PlainDate :=
  addDays date (-days)

/--
Adds a given number of weeks to a `PlainDate`.
-/

@[inline]
def addWeeks (date : PlainDate) (weeks : Week.Offset) : PlainDate :=
  let dateDays := date.toDaysSinceUNIXEpoch
  let daysToAdd := weeks.toDays
  ofDaysSinceUNIXEpoch (dateDays + daysToAdd)

/--
Subtracts a given number of weeks from a `PlainDate`.
-/
@[inline]
def subWeeks (date : PlainDate) (weeks : Week.Offset) : PlainDate :=
  addWeeks date (-weeks)
/--
Adds a given number of months to a `PlainDate`, clipping the day to the last valid day of the month.
-/
def addMonthsClip (date : PlainDate) (months : Month.Offset) : PlainDate :=
  let totalMonths := (date.month.toOffset - 1) + months
  let totalMonths : Int := totalMonths
  let wrappedMonths := Bounded.LE.byEmod totalMonths 12 (by decide) |>.add 1
  let yearsOffset := totalMonths / 12
  PlainDate.clip (date.year.add yearsOffset) wrappedMonths date.day

/--
Subtracts `Month.Offset` from a `PlainDate`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (date : PlainDate) (months : Month.Offset) : PlainDate :=
  addMonthsClip date (-months)

/--
Creates a `PlainDate` by rolling over the extra days to the next month.
-/
def rollOver (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : PlainDate :=
  clip year month 1 |>.addDays (day.toOffset - 1)

/--
Creates a new `PlainDate` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : PlainDate) (days : Day.Ordinal) : PlainDate :=
  clip dt.year dt.month days

/--
Creates a new `PlainDate` by adjusting the day of the month to the given `days` value, with any
out-of-range days rolled over to the next month or year as needed.
-/
@[inline]
def withDaysRollOver (dt : PlainDate) (days : Day.Ordinal) : PlainDate :=
  rollOver dt.year dt.month days

/--
Creates a new `PlainDate` by adjusting the month to the given `month` value.
The day remains unchanged, and any invalid days for the new month will be handled according to the `clip` behavior.
-/
@[inline]
def withMonthClip (dt : PlainDate) (month : Month.Ordinal) : PlainDate :=
  clip dt.year month dt.day

/--
Creates a new `PlainDate` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : PlainDate) (month : Month.Ordinal) : PlainDate :=
  rollOver dt.year month dt.day

/--
Creates a new `PlainDate` by adjusting the year to the given `year` value. The month and day remain unchanged,
and any invalid days for the new year will be handled according to the `clip` behavior.
-/
@[inline]
def withYearClip (dt : PlainDate) (year : Year.Offset) : PlainDate :=
  clip year dt.month dt.day

/--
Creates a new `PlainDate` by adjusting the year to the given `year` value. The month and day are rolled
over to the next valid month and day if necessary.
-/
@[inline]
def withYearRollOver (dt : PlainDate) (year : Year.Offset) : PlainDate :=
  rollOver year dt.month dt.day

/--
Adds a given number of months to a `PlainDate`, rolling over any excess days into the following month.
-/
def addMonthsRollOver (date : PlainDate) (months : Month.Offset) : PlainDate :=
  addMonthsClip (clip date.year date.month 1) months |>.addDays (date.day.toOffset - 1)

/--
Subtracts `Month.Offset` from a `PlainDate`, rolling over excess days as needed.
-/
@[inline]
def subMonthsRollOver (date : PlainDate) (months : Month.Offset) : PlainDate :=
  addMonthsRollOver date (-months)

/--
Adds `Year.Offset` to a `PlainDate`, rolling over excess days to the next month, or next year.
-/
@[inline]
def addYearsRollOver (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsRollOver date (years.mul 12)

/--
Subtracts `Year.Offset` from a `PlainDate`, rolling over excess days to the next month.
-/
@[inline]
def subYearsRollOver (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsRollOver date (- years.mul 12)

/--
Adds `Year.Offset` to a `PlainDate`, clipping the day to the last valid day of the month.
-/
@[inline]
def addYearsClip (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsClip date (years.mul 12)

/--
Subtracts `Year.Offset` from a `PlainDate`, clipping the day to the last valid day of the month.
-/
@[inline]
def subYearsClip (date : PlainDate) (years : Year.Offset) : PlainDate :=
  addMonthsClip date (- years.mul 12)

instance : HAdd PlainDate Day.Offset PlainDate where
  hAdd := addDays

instance : HSub PlainDate Day.Offset PlainDate where
  hSub := subDays

instance : HAdd PlainDate Week.Offset PlainDate where
  hAdd := addWeeks

instance : HSub PlainDate Week.Offset PlainDate where
  hSub := subWeeks

end PlainDate
end Time
end Std
