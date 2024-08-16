/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Internal
import Std.Time.Date.Basic

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
`LocalDate` represents a date in the Year-Month-Day (YMD) format. It encapsulates the year, month,
and day components, with validation to ensure the date is valid.
-/
structure LocalDate where

  /--
  The year component of the date. It is represented as an `Offset` type from `Year`.
  -/
  year : Year.Offset

  /--
  The month component of the date. It is represented as an `Ordinal` type from `Month`.
  -/
  month : Month.Ordinal

  /--
  The day component of the date. It is represented as an `Ordinal` type from `Day`.
  -/
  day : Day.Ordinal

  /--
  Validates the date by ensuring that the year, month, and day form a correct and valid date.
  -/
  valid : year.Valid month day

  deriving Repr

instance : BEq LocalDate where
  beq x y := x.day == y.day && x.month == y.month && x.year == y.year

namespace LocalDate

/--
Creates a `LocalDate` by clipping the day to ensure validity. This function forces the date to be
valid by adjusting the day to fit within the valid range to fit the given month and year.
-/
def clip (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : LocalDate :=
  let ⟨day, valid⟩ := month.clipDay year.isLeap day
  LocalDate.mk year month day valid

instance : Inhabited LocalDate where
  default := clip 0 1 1

/--
Creates a new `LocalDate` from year, month, and day components.
-/
def ofYearMonthDay (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Option LocalDate :=
  if valid : year.Valid month day
    then some (LocalDate.mk year month day valid)
    else none

/--
Creates a `LocalDate` from a year and a day ordinal within that year.
-/
def ofYearOrdinal (year : Year.Offset) (ordinal : Day.Ordinal.OfYear year.isLeap) : LocalDate :=
  let ⟨⟨month, day⟩, valid⟩ := Month.Ordinal.ofOrdinal ordinal
  LocalDate.mk year month day valid

/--
Creates a `LocalDate` from the number of days since the UNIX epoch (January 1st, 1970).
-/
def ofDaysSinceUNIXEpoch (day : Day.Offset) : LocalDate :=
  let z := day.toInt + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp : Int := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5
  let m := mp + (if mp < 10 then 3 else -9)
  let y := y + (if m <= 2 then 1 else 0)

  .clip y (.clip m (by decide)) (.clip (d + 1) (by decide))

/--
Calculates the `Weekday` of a given `LocalDate` using Zeller's Congruence for the Gregorian calendar.
-/
def weekday (date : LocalDate) : Weekday :=
  let q := date.day.toInt
  let m := date.month.toInt
  let y := date.year.toInt

  let y := if m < 2 then y - 1 else y
  let m := if m < 2 then m + 12 else m

  let k := y % 100
  let j := y / 100
  let part := q + (13 * (m + 1)) / 5 + k + (k / 4)
  let h :=  if y ≥ 1582 then part + (j/4) - 2*j else part + 5 - j
  let d := (h + 5) % 7

  .ofFin ⟨d.toNat % 7, Nat.mod_lt d.toNat (by decide)⟩

/--
Converts a `LocalDate` to the number of days since the UNIX epoch.
-/
def toDaysSinceUNIXEpoch (date : LocalDate) : Day.Offset :=
  let y : Int := if date.month.toInt > 2 then date.year else date.year.toInt - 1
  let era : Int := (if y ≥ 0 then y else y - 399) / 400
  let yoe : Int := y - era * 400
  let m : Int := date.month.toInt
  let d : Int := date.day.toInt
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy

  .ofInt (era * 146097 + doe - 719468)

/--
Calculates the difference in years between a `LocalDate` and a given year.
-/
def yearsSince (date : LocalDate) (year : Year.Offset) : Year.Offset :=
  date.year - year

/--
Adds a given number of days to a `LocalDate`.
-/
@[inline]
def addDays (date : LocalDate) (days : Day.Offset) : LocalDate :=
  let dateDays := date.toDaysSinceUNIXEpoch
  ofDaysSinceUNIXEpoch (Add.add dateDays days)

/--
Subtracts a given number of days from a `LocalDate`.
-/
@[inline]
def subDays (date : LocalDate) (days : Day.Offset) : LocalDate :=
  addDays date (-days)

/--
Adds a given number of months to a `LocalDate`, clipping the day to the last valid day of the month.
-/
def addMonthsClip (date : LocalDate) (months : Month.Offset) : LocalDate :=
  let yearsOffset := months.div 12
  let monthOffset := Bounded.LE.byMod months 12 (by decide)
  let months := date.month.addBounds monthOffset

  let (yearsOffset, months) : Year.Offset × Month.Ordinal := by
    if h₁ : months.val > 12 then
      let months := months |>.truncateBottom h₁ |>.sub 12
      exact (yearsOffset.add 1, months.expandTop (by decide))
    else if h₂ : months.val < 1 then
      let months := months |>.truncateTop (Int.le_sub_one_of_lt h₂) |>.add 12
      exact (yearsOffset.sub 1, months.expandBottom (by decide))
    else
      exact (yearsOffset, months.truncateTop (Int.not_lt.mp h₁) |>.truncateBottom (Int.not_lt.mp h₂))

  LocalDate.clip (date.year.add yearsOffset) months date.day

/--
Subtracts `Month.Offset` from a `LocalDate`, it clips the day to the last valid day of that month.
-/
@[inline]
def subMonthsClip (date : LocalDate) (months : Month.Offset) : LocalDate :=
  addMonthsClip date (-months)

/--
Adds a given number of months to a `LocalDate`, rolling over any excess days into the following month.
-/
def addMonthsRollOver (date : LocalDate) (months : Month.Offset) : LocalDate :=
  let yearsOffset := months.div 12
  let monthOffset := Bounded.LE.byMod months 12 (by decide)
  let months := date.month.addBounds monthOffset

  let (yearsOffset, months) : Year.Offset × Month.Ordinal := by
    if h₁ : months.val > 12 then
      let months := months |>.truncateBottom h₁ |>.sub 12
      exact (yearsOffset.add 1, months.expandTop (by decide))
    else if h₂ : months.val < 1 then
      let months := months |>.truncateTop (Int.le_sub_one_of_lt h₂) |>.add 12
      exact (yearsOffset.sub 1, months.expandBottom (by decide))
    else
      exact (yearsOffset, months.truncateTop (Int.not_lt.mp h₁) |>.truncateBottom (Int.not_lt.mp h₂))

  let year : Year.Offset := date.year.add yearsOffset
  let ⟨days, proof⟩ := Month.Ordinal.days year.isLeap months

  if h : days.val ≥ date.day.val then
    let p : year.Valid months date.day := by
      simp_all [Year.Offset.Valid, Month.Ordinal.Valid]
      exact Int.le_trans h proof
    dbg_trace s!"roll {days.val} {date.day.val}"
    LocalDate.mk year months date.day p
  else
    let roll : Day.Offset := UnitVal.mk (date.day.val - days.toInt)
    let date := LocalDate.clip (date.year.add yearsOffset) months date.day
    let days := date.toDaysSinceUNIXEpoch + roll
    LocalDate.ofDaysSinceUNIXEpoch days

/--
Subtracts `Month.Offset` from a `LocalDate`, rolling over excess days as needed.
-/
@[inline]
def subMonthsRollOver (date : LocalDate) (months : Month.Offset) : LocalDate :=
  addMonthsRollOver date (-months)

/--
Adds `Year.Offset` to a `LocalDate`, rolling over excess days to the next month, or next year.
-/
@[inline]
def addYearsRollOver (date : LocalDate) (years : Year.Offset) : LocalDate :=
  addMonthsRollOver date (years.mul 12)

/--
Subtracts `Year.Offset` from a `LocalDate`, rolling over excess days to the next month.
-/
@[inline]
def subYearsRollOver (date : LocalDate) (years : Year.Offset) : LocalDate :=
  addMonthsRollOver date (- years.mul 12)

/--
Adds `Year.Offset` to a `LocalDate`, clipping the day to the last valid day of the month.
-/
@[inline]
def addYearsClip (date : LocalDate) (years : Year.Offset) : LocalDate :=
  addMonthsClip date (years.mul 12)

/--
Subtracts `Year.Offset` from a `LocalDate`, clipping the day to the last valid day of the month.
-/
@[inline]
def subYearsClip (date : LocalDate) (years : Year.Offset) : LocalDate :=
  addMonthsClip date (- years.mul 12)

instance : HAdd LocalDate Day.Offset LocalDate where
  hAdd date day := ofDaysSinceUNIXEpoch (toDaysSinceUNIXEpoch date + day)

end LocalDate
end Time
end Std
