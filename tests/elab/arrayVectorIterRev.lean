import Std.Data.Iterators

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval #[1, 2, 3].iterRev.toList

/-- info: [3, 2, 1] -/
#guard_msgs in
#eval #[1, 2, 3].toVector.iterRev.toList

/-- info: [2, 1] -/
#guard_msgs in
#eval #[1, 2, 3].iterRevFromIdx 1 |>.toList

/-- info: [2, 1] -/
#guard_msgs in
#eval #[1, 2, 3].toVector.iterRevFromIdx 1 |>.toList
