import Std.Internal.Rat

open Std.Internal

/-- info: 1 -/
#guard_msgs in
#eval ((14:Rat)/11).floor

/-- info: -2 -/
#guard_msgs in
#eval ((-14:Rat)/11).floor

/-- info: 2 -/
#guard_msgs in
#eval ((14:Rat)/11).ceil

/-- info: -1 -/
#guard_msgs in
#eval ((-14:Rat)/11).ceil

/-- info: (5 : Rat)/2 -/
#guard_msgs in
#eval (1/6 : Rat) + 2 + 1/3

/-- info: true -/
#guard_msgs in
#eval (1/6 : Rat) ≤ 1/3
