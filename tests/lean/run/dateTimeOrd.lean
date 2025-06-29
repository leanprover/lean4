import Std.Time

open Std.Time

def strictly_ordered {α} [Ord α] : List α → Bool
  | [] => true
  | [_] => true
  | x :: y :: tail => compare x y = .lt && strictly_ordered (y :: tail)

def plainDate1 := PlainDate.ofYearMonthDay? 2020 03 02 |>.get!
def plainDate2 := PlainDate.ofYearMonthDay? 2025 01 02 |>.get!
def plainDate3 := PlainDate.ofYearMonthDay? 2025 02 01 |>.get!

example : Std.TransOrd PlainDate := inferInstance
example : Std.LawfulEqOrd PlainDate := inferInstance
example : Std.LawfulBEqOrd PlainDate := inferInstance
example : strictly_ordered
  [PlainDate.ofYearMonthDay? 2020 03 02 |>.get!,
   PlainDate.ofYearMonthDay? 2025 01 02 |>.get!,
   PlainDate.ofYearMonthDay? 2025 02 01 |>.get!] := by decide

def plainTime1 := PlainTime.ofHourMinuteSecondsNano 0 0 0 1
def plainTime2 := PlainTime.ofHourMinuteSecondsNano 0 0 1 0
def plainTime3 := PlainTime.ofHourMinuteSecondsNano 0 1 0 0
def plainTime4 := PlainTime.ofHourMinuteSecondsNano 1 0 0 0

example : Std.TransOrd PlainTime := inferInstance
example : Std.LawfulEqOrd PlainTime := inferInstance
example : Std.LawfulBEqOrd PlainTime := inferInstance
example : strictly_ordered
  [PlainTime.ofHourMinuteSecondsNano 0 0 0 1,
   PlainTime.ofHourMinuteSecondsNano 0 0 1 0,
   PlainTime.ofHourMinuteSecondsNano 0 1 0 0,
   PlainTime.ofHourMinuteSecondsNano 1 0 0 0] := by decide

example : Std.TransOrd (DateTime TimeZone.GMT) := inferInstance
example : Std.LawfulBEqOrd (DateTime TimeZone.GMT) := inferInstance

-- We cannot use `decide` here because the reduction gets stuck.
/-- info: true -/
#guard_msgs in
#eval strictly_ordered <|
  ["Sat Jan 01 01:01:02 2025",
   "Sat Jan 01 01:02:01 2025",
   "Sat Jan 01 02:01:01 2025",
   "Sat Jan 02 01:01:01 2025",
   "Sat Feb 01 01:01:01 2025",
   "Sat Jan 01 01:01:01 2026"].map (DateTime.fromAscTimeString . |>.toOption.get!)
