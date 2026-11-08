import Std.Time
open Std.Time

/-!
Checks that `Month.Ordinal.toDays`, `toHours`, `toMinutes` and `toSeconds` give the time from the
start of the year to the start of the month, for every month of a common and a leap year.
-/

def firstDays (year : Int) : List PlainDate :=
  (List.range 12).map fun k => (PlainDate.ofYearMonthDayClip year 1 1).addMonthsClip (.ofNat k)

/-- info: [0, 31, 59, 90, 120, 151, 181, 212, 243, 273, 304, 334] -/
#guard_msgs in #eval (firstDays 2023).map fun d => (d.month.toDays false).val

/-- info: [0, 31, 60, 91, 121, 152, 182, 213, 244, 274, 305, 335] -/
#guard_msgs in #eval (firstDays 2024).map fun d => (d.month.toDays true).val

-- The first day of each month is one day after the days before it.
/-- info: true -/
#guard_msgs in
#eval (firstDays 2023 ++ firstDays 2024).all fun d =>
  let leap := d.year.isLeap
  (d.month.toDays leap).val + 1 == d.dayOfYear.val &&
  (d.month.toHours leap).val == (d.month.toDays leap).val * 24 &&
  (d.month.toMinutes leap).val == (d.month.toDays leap).val * 1440 &&
  (d.month.toSeconds leap).val == (d.month.toDays leap).val * 86400
