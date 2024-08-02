/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Lean.Time.Date.Unit.Year
import Lean.Time.Date.Unit.WeekOfYear
import Lean.Time.Date.Scalar
import Lean.Time.Date.Date

namespace Lean
namespace Date

/--
`WeekDate` represents a date using a combination of a week of the year and the year.
-/
structure WeekDate where
  year : Year.Offset
  week : WeekOfYear.Ordinal
  deriving Repr, BEq, Inhabited

namespace WeekDate

/--
Converts a `WeekDate` to a `Scalar`.
-/
def toScalar (wd : WeekDate) : Scalar :=
  let days := wd.year.toInt * 365 + wd.week.val * 7
  Scalar.ofDays days

/--
Creates a `WeekDate` from a `Scalar`.
-/
def fromScalar (scalar : Scalar) : WeekDate :=
  let totalDays := scalar.toDays
  let year := totalDays / 365
  let week :=
    Bounded.LE.byEmod totalDays 365 (by decide)
    |>.div 7 (by decide)
    |>.add 1
  { year := year, week := week }
