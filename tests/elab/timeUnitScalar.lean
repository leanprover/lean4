import Std.Time
open Std.Time

/-!
Multiplication and division of time unit offsets and `Duration`s by `Nat` and `Int` scalars,
keeping the unit (#10198). Division rounds toward zero, like the unit conversions.
-/

def s : Second.Offset := 90
def neg : Second.Offset := -90

/-- info: 180 -/
#guard_msgs in #eval s * 2

/-- info: 180 -/
#guard_msgs in #eval 2 * s

/-- info: -270 -/
#guard_msgs in #eval s * (-3 : Int)

/-- info: -270 -/
#guard_msgs in #eval (-3 : Int) * s

/-- info: 45 -/
#guard_msgs in #eval s / 2

/-- info: -22 -/
#guard_msgs in #eval s / (-4 : Int)

/-- info: -1 -/
#guard_msgs in #eval neg / 60

/-- info: 0 -/
#guard_msgs in #eval s / 0

/-- info: 181 -/
#guard_msgs in #eval s * 2 + 1

-- Mixed with the unit's own arithmetic, the result keeps the unit's type.
example : Second.Offset := s * 2 - s / 3

-- `/` agrees with the unit conversions, which also round toward zero.
#guard [-121, -120, -119, -1, 0, 1, 119, 120, 121].all fun n =>
  ((Second.Offset.ofInt n / 60 : Second.Offset).val == (Second.Offset.ofInt n).toMinutes.val)

/-- info: 3000000 -/
#guard_msgs in #eval (1500 : Nanosecond.Offset) * 2000

/-- info: 333 -/
#guard_msgs in #eval (1000 : Millisecond.Offset) / 3

/-- info: 150 -/
#guard_msgs in #eval (30 : Minute.Offset) * 5

/-- info: 12 -/
#guard_msgs in #eval (36 : Hour.Offset) / 3

/-- info: 14 -/
#guard_msgs in #eval 2 * (7 : Day.Offset)

/-- info: 2 -/
#guard_msgs in #eval (5 : Week.Offset) / 2

def d : Duration := Duration.ofSeconds 90

/-- info: "180s" -/
#guard_msgs in #eval d * 2

/-- info: "180s" -/
#guard_msgs in #eval 2 * d

/-- info: "-180s" -/
#guard_msgs in #eval d * (-2 : Int)

/-- info: "30s" -/
#guard_msgs in #eval d / 3

/-- info: "-30s" -/
#guard_msgs in #eval d / (-3 : Int)

/-- info: "12.857142857s" -/
#guard_msgs in #eval d / 7

/-- info: "-12.857142857s" -/
#guard_msgs in #eval Duration.ofSeconds (-90) / 7
