/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.UnitVal
import Lean.Time.Date.Basic
import Lean.Time.Date.Scalar

namespace Lean
namespace Date

/--
Date in YMD format.
-/
structure Date where
  year : Year.Offset
  month : Month.Ordinal
  day : Day.Ordinal
  valid : year.valid month day
  deriving Repr

namespace Date

/--
Force the date to be valid.
-/
def force (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Date :=
  let ⟨day, valid⟩ := month.forceDay year.isLeap day
  Date.mk year month day valid

/--
Creates a new `Date` using YMD.
-/
def ofYearMonthDay (year : Year.Offset) (month : Month.Ordinal) (day : Day.Ordinal) : Option Date :=
  if valid : year.valid month day
    then some (Date.mk year month day valid)
    else none

/--
Creates a new `Date` using YO.
-/
def ofYearOrdinal (year : Year.Offset) (ordinal : Day.Ordinal.OfYear year.isLeap) : Date :=
  let ⟨⟨month, day⟩, valid⟩ := ordinal.toMonthAndDay
  Date.mk year month day valid

/--
Creates a new `Date` using the `Day.Offset` which `0` corresponds the UNIX Epoch.
-/
def ofDaysSinceUNIXEpoch (day : Day.Offset) : Date :=
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

  .force y (.force m (by decide)) (.force (d + 1) (by decide))

/--
Returns the `Weekday` of a `Date`.
-/
def weekday (date : Date) : Weekday :=
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
Returns the `Weekday` of a `Date` using Zeller's Congruence for the Julian calendar.
-/
def weekdayJulian (date : Date) : Weekday :=
  let month := date.month.toInt
  let year := date.year.toInt

  let q := date.day.toInt
  let m := if month < 3 then month + 12 else month
  let y := if month < 3 then year - 1 else year

  let k := y % 100
  let j := y / 100

  let h := (q + (13 * (m + 1)) / 5 + k + (k / 4) + 5 - j) % 7
  let d := (h + 5 - 1) % 7

  .ofFin ⟨d.toNat % 7, Nat.mod_lt d.toNat (by decide)⟩

/--
Convert `Date` to `Day.Offset` since the UNIX Epoch.
-/
def toDaysSinceUNIXEpoch (date : Date) : Day.Offset :=
  let y : Int := if date.month.toInt > 2 then date.year else date.year.toInt - 1
  let era : Int := (if y ≥ 0 then y else y - 399) / 400
  let yoe : Int := y - era * 400
  let m : Int := date.month.toInt
  let d : Int := date.day.toInt
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy

  .ofInt (era * 146097 + doe - 719468)

/--
Returns the `Scalar` starting from the UNIX epoch.
-/
def toScalar (date : Date) : Scalar :=
  ⟨toDaysSinceUNIXEpoch date⟩

/--
Creates a new `Date` from a `Scalar` that begins on the epoch.
-/
def ofScalar (scalar : Scalar) : Date :=
  ofDaysSinceUNIXEpoch scalar.day

/--
Calculate the Year.Offset from a Date
-/
def yearsSince (date : Date) (year : Year.Offset) : Year.Offset :=
  date.year - year

instance : HAdd Date Day.Offset Date where
  hAdd date day :=  ofScalar (toScalar date + ⟨day⟩)

instance : HAdd Date Scalar Date where
  hAdd date day := ofScalar (toScalar date + day)
