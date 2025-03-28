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
open Std.Time
open Internal
open Lean

set_option linter.all true

/--
`PlainDate` represents a date in the Year-Month-Day (YMD) format. It encapsulates the year, month,
and day components, with validation to ensure the date is valid.
-/
@[ext]
structure PlainDate where

  /-- The year component of the date. It is represented as an `Offset` type from `Year`. -/
  year : Year.Offset

  /-- The month component of the date. It is represented as an `Ordinal` type from `Month`. -/
  month : Month.Ordinal

  /-- The day component of the date. It is represented as an `Ordinal` type from `Day`. -/
  day : Day.Ordinal

  /-- Validates the date by ensuring that the year, month, and day form a correct and valid date. -/
  valid : year.Valid month day
deriving Repr, DecidableEq

instance : Inhabited PlainDate where
  default := ⟨1, 1, 1, by decide⟩

instance : Ord PlainDate where
  compare := compareLex (compareOn (·.year)) <| compareLex (compareOn (·.month)) (compareOn (·.day))

theorem PlainDate.compare_def :
    compare (α := PlainDate) =
      compareLex (compareOn (·.year)) (compareLex (compareOn (·.month)) (compareOn (·.day))) := rfl

instance : TransOrd PlainDate := inferInstanceAs <| TransCmp (compareLex _ _)

instance : LawfulEqOrd PlainDate where
  eq_of_compare {a b} h := by
    simp only [PlainDate.compare_def, compareLex_eq_eq] at h
    ext
    · exact LawfulEqOrd.eq_of_compare h.1
    · exact LawfulEqOrd.eq_of_compare h.2.1
    · exact LawfulEqOrd.eq_of_compare h.2.2

namespace PlainDate

/--
Creates a `PlainDate` by clipping the day to ensure validity. This function forces the date to be
valid by adjusting the day to fit within the valid range to fit the given month and year.
-/
@[inline]
def ofYearMonthDayClip (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : PlainDate :=
  let day := month.clipDay year.isLeap day
  PlainDate.mk year month day Month.Ordinal.valid_clipDay

instance : Inhabited PlainDate where
  default := mk 0 1 1 (by decide)

/--
Creates a new `PlainDate` from year, month, and day components.
-/
@[inline]
def ofYearMonthDay? (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Option PlainDate :=
  if valid : year.Valid month day
    then some (PlainDate.mk year month day valid)
    else none

/--
Creates a `PlainDate` from a year and a day ordinal within that year.
-/
@[inline]
def ofYearOrdinal (year : Year.Offset) (ordinal : Day.Ordinal.OfYear year.isLeap) : PlainDate :=
  let ⟨⟨month, day⟩, proof⟩ := ValidDate.ofOrdinal ordinal
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
  .ofYearMonthDayClip y (.clip m (by decide)) (.clip d (by decide))

/--
Returns the unaligned week of the month for a `PlainDate` (day divided by 7, plus 1).
-/
def weekOfMonth (date : PlainDate) : Bounded.LE 1 5 :=
  date.day.sub 1 |>.ediv 7 (by decide) |>.add 1

/--
Determines the quarter of the year for the given `PlainDate`.
-/
def quarter (date : PlainDate) : Bounded.LE 1 4 :=
  date.month.sub 1 |>.ediv 3 (by decide) |>.add 1

/--
Transforms a `PlainDate` into a `Day.Ordinal.OfYear`.
-/
def dayOfYear (date : PlainDate) : Day.Ordinal.OfYear date.year.isLeap :=
  ValidDate.dayOfYear ⟨(date.month, date.day), date.valid⟩

/--
Determines the era of the given `PlainDate` based on its year.
-/
@[inline]
def era (date : PlainDate) : Year.Era :=
  date.year.era

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
  PlainDate.ofYearMonthDayClip (date.year.add yearsOffset) wrappedMonths date.day

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
  ofYearMonthDayClip year month 1 |>.addDays (day.toOffset - 1)

/--
Creates a new `PlainDate` by adjusting the year to the given `year` value. The month and day remain unchanged,
and any invalid days for the new year will be handled according to the `clip` behavior.
-/
@[inline]
def withYearClip (dt : PlainDate) (year : Year.Offset) : PlainDate :=
  ofYearMonthDayClip year dt.month dt.day

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
  addMonthsClip (ofYearMonthDayClip date.year date.month 1) months
  |>.addDays (date.day.toOffset - 1)

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

/--
Creates a new `PlainDate` by adjusting the day of the month to the given `days` value, with any
out-of-range days clipped to the nearest valid date.
-/
@[inline]
def withDaysClip (dt : PlainDate) (days : Day.Ordinal) : PlainDate :=
  ofYearMonthDayClip dt.year dt.month days

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
  ofYearMonthDayClip dt.year month dt.day

/--
Creates a new `PlainDate` by adjusting the month to the given `month` value.
The day is rolled over to the next valid month if necessary.
-/
@[inline]
def withMonthRollOver (dt : PlainDate) (month : Month.Ordinal) : PlainDate :=
  rollOver dt.year month dt.day

/--
Calculates the `Weekday` of a given `PlainDate` using Zeller's Congruence for the Gregorian calendar.
-/
def weekday (date : PlainDate) : Weekday :=
  let days := date.toDaysSinceUNIXEpoch.val
  let res := if days ≥ -4 then (days + 4) % 7 else (days + 5) % 7 + 6
  .ofOrdinal (Bounded.LE.ofNatWrapping res (by decide))

/--
Determines the week of the month for the given `PlainDate`. The week of the month is calculated based
on the day of the month and the weekday. Each week starts on Monday because the entire library is
based on the Gregorian Calendar.
-/
def alignedWeekOfMonth (date : PlainDate) : Week.Ordinal.OfMonth :=
  let weekday := date.withDaysClip 1 |>.weekday |>.toOrdinal |>.sub 1
  let days := date.day |>.sub 1 |>.addBounds weekday
  days |>.ediv 7 (by decide) |>.add 1

/--
Sets the date to the specified `desiredWeekday`. If the `desiredWeekday` is the same as the current weekday,
the original `date` is returned without modification. If the `desiredWeekday` is in the future, the
function adjusts the date forward to the next occurrence of that weekday.
-/
def withWeekday (date : PlainDate) (desiredWeekday : Weekday) : PlainDate :=
  let weekday := date |>.weekday |>.toOrdinal
  let offset := desiredWeekday.toOrdinal |>.subBounds weekday

  let offset : Bounded.LE 0 6 :=
    if h : offset.val < 0 then
      offset.truncateTop (Int.le_sub_one_of_lt h) |>.addBounds (.exact 7)
      |>.expandBottom (by decide)
    else
      offset.truncateBottom (Int.not_lt.mp h)
      |>.expandTop (by decide)

  date.addDays (Day.Offset.ofInt offset.toInt)

/--
Calculates the week of the year starting Monday for a given year.
-/
def weekOfYear (date : PlainDate) : Week.Ordinal :=
  let y := date.year

  let w := Bounded.LE.exact 10
    |>.addBounds date.dayOfYear
    |>.subBounds date.weekday.toOrdinal
    |>.ediv 7 (by decide)

  if h : w.val < 1 then
    (y-1).weeks |>.expandBottom (by decide)
  else if h₁ : w.val > y.weeks.val then
    .ofNat' 1 (by decide)
  else
    let h := Int.not_lt.mp h
    let h₁ := Int.not_lt.mp h₁
    let w := w.truncateBottom h |>.truncateTop (Int.le_trans h₁ y.weeks.property.right)
    w

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
