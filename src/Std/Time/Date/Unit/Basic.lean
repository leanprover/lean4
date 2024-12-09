/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sofia Rodrigues
-/
prelude
import Std.Time.Date.Unit.Day
import Std.Time.Date.Unit.Month
import Std.Time.Date.Unit.Year
import Std.Time.Date.Unit.Weekday
import Std.Time.Date.Unit.Week

/-!
This module defines various units used for measuring, counting, and converting between days, months,
years, weekdays, and weeks of the year.

The units are organized into types representing these time-related concepts, with operations provided
to facilitate conversions and manipulations between them.
-/

namespace Std
namespace Time
open Internal

namespace Day.Offset

/--
Convert `Week.Offset` into `Day.Offset`.
-/
@[inline]
def ofWeeks (week : Week.Offset) : Day.Offset :=
  week.mul 7

/--
Convert `Day.Offset` into `Week.Offset`.
-/
@[inline]
def toWeeks (day : Day.Offset) : Week.Offset :=
  day.ediv 7

end Day.Offset
