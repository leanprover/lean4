/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date.Unit.Year
import Std.Time.Date.Unit.WeekOfYear
import Std.Time.Date.LocalDate

namespace Std
namespace Time
open Internal

set_option linter.all true

/--
`WeekDate` represents a date using a combination of a week of the year and the year.
-/
structure WeekDate where

  /--
  The year component of the date. It is represented as an `Offset` type from `Year`.
  -/
  year : Year.Offset

  /--
  The week of the year component. It is represented as an `Ordinal` type from `WeekOfYear`.
  -/
  week : WeekOfYear.Ordinal
  deriving Repr, BEq, Inhabited

namespace WeekDate

/--
Converts a `WeekDate` to a `Day.Offset`.
-/
def toDays (wd : WeekDate) : Day.Offset :=
  let days := wd.year.toInt * 365 + wd.week.val * 7
  UnitVal.mk days

/--
Creates a `WeekDate` from a `Day.Offset`.
-/
def fromDays (scalar : Day.Offset) : WeekDate :=
  let totalDays := scalar.val
  let year := totalDays / 365
  let week := Bounded.LE.byEmod totalDays 365 (by decide) |>.ediv 7 (by decide) |>.add 1
  { year := year, week := week }

end WeekDate
end Time
end Std
