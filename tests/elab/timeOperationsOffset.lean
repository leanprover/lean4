import Std.Time
open Std.Time

/--
info: 2
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Nanosecond.Offset)

/--
info: 2
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Nanosecond.Offset)

/--
info: 1000001
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Millisecond.Offset)

/--
info: 1000000001
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Second.Offset)

/--
info: 60000000001
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Minute.Offset)

/--
info: 3600000000001
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Hour.Offset)

/--
info: 86400000000001
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Day.Offset)

/--
info: 604800000000001
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) + (1 : Week.Offset)

/--
info: 1000001
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) + (1 : Nanosecond.Offset)

/--
info: 2
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) + (1 : Millisecond.Offset)

/--
info: 1001
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) + (1 : Second.Offset)

/--
info: 60001
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) + (1 : Minute.Offset)

/--
info: 3600001
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) + (1 : Hour.Offset)

/--
info: 86400001
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) + (1 : Day.Offset)

/--
info: 604800001
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) + (1 : Week.Offset)

/--
info: 1000000001
-/
#guard_msgs in
#eval (1 : Second.Offset) + (1 : Nanosecond.Offset)

/--
info: 1001
-/
#guard_msgs in
#eval (1 : Second.Offset) + (1 : Millisecond.Offset)

/--
info: 2
-/
#guard_msgs in
#eval (1 : Second.Offset) + (1 : Second.Offset)

/--
info: 61
-/
#guard_msgs in
#eval (1 : Second.Offset) + (1 : Minute.Offset)

/--
info: 3601
-/
#guard_msgs in
#eval (1 : Second.Offset) + (1 : Hour.Offset)

/--
info: 86401
-/
#guard_msgs in
#eval (1 : Second.Offset) + (1 : Day.Offset)

/--
info: 604801
-/
#guard_msgs in
#eval (1 : Second.Offset) + (1 : Week.Offset)

/--
info: 60000000001
-/
#guard_msgs in
#eval (1 : Minute.Offset) + (1 : Nanosecond.Offset)

/--
info: 60001
-/
#guard_msgs in
#eval (1 : Minute.Offset) + (1 : Millisecond.Offset)

/--
info: 61
-/
#guard_msgs in
#eval (1 : Minute.Offset) + (1 : Second.Offset)

/--
info: 2
-/
#guard_msgs in
#eval (1 : Minute.Offset) + (1 : Minute.Offset)

/--
info: 61
-/
#guard_msgs in
#eval (1 : Minute.Offset) + (1 : Hour.Offset)

/--
info: 1441
-/
#guard_msgs in
#eval (1 : Minute.Offset) + (1 : Day.Offset)

/--
info: 10081
-/
#guard_msgs in
#eval (1 : Minute.Offset) + (1 : Week.Offset)

/--
info: 3600000000001
-/
#guard_msgs in
#eval (1 : Hour.Offset) + (1 : Nanosecond.Offset)

/--
info: 3600001
-/
#guard_msgs in
#eval (1 : Hour.Offset) + (1 : Millisecond.Offset)

/--
info: 3601
-/
#guard_msgs in
#eval (1 : Hour.Offset) + (1 : Second.Offset)

/--
info: 61
-/
#guard_msgs in
#eval (1 : Hour.Offset) + (1 : Minute.Offset)

/--
info: 2
-/
#guard_msgs in
#eval (1 : Hour.Offset) + (1 : Hour.Offset)

/--
info: 25
-/
#guard_msgs in
#eval (1 : Hour.Offset) + (1 : Day.Offset)

/--
info: 169
-/
#guard_msgs in
#eval (1 : Hour.Offset) + (1 : Week.Offset)

/--
info: 86400000000001
-/
#guard_msgs in
#eval (1 : Day.Offset) + (1 : Nanosecond.Offset)

/--
info: 86400001
-/
#guard_msgs in
#eval (1 : Day.Offset) + (1 : Millisecond.Offset)

/--
info: 86401
-/
#guard_msgs in
#eval (1 : Day.Offset) + (1 : Second.Offset)

/--
info: 1441
-/
#guard_msgs in
#eval (1 : Day.Offset) + (1 : Minute.Offset)

/--
info: 25
-/
#guard_msgs in
#eval (1 : Day.Offset) + (1 : Hour.Offset)

/--
info: 2
-/
#guard_msgs in
#eval (1 : Day.Offset) + (1 : Day.Offset)

/--
info: 8
-/
#guard_msgs in
#eval (1 : Day.Offset) + (1 : Week.Offset)

/--
info: 604800000000001
-/
#guard_msgs in
#eval (1 : Week.Offset) + (1 : Nanosecond.Offset)

/--
info: 604800001
-/
#guard_msgs in
#eval (1 : Week.Offset) + (1 : Millisecond.Offset)

/--
info: 604801
-/
#guard_msgs in
#eval (1 : Week.Offset) + (1 : Second.Offset)

/--
info: 10081
-/
#guard_msgs in
#eval (1 : Week.Offset) + (1 : Minute.Offset)

/--
info: 169
-/
#guard_msgs in
#eval (1 : Week.Offset) + (1 : Hour.Offset)

/--
info: 8
-/
#guard_msgs in
#eval (1 : Week.Offset) + (1 : Day.Offset)

/--
info: 2
-/
#guard_msgs in
#eval (1 : Week.Offset) + (1 : Week.Offset)

/--
info: 0
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) - (1 : Nanosecond.Offset)

/--
info: -999999
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) - (1 : Millisecond.Offset)

/--
info: -999999999
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) - (1 : Second.Offset)

/--
info: -59999999999
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) - (1 : Minute.Offset)

/--
info: -3599999999999
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) - (1 : Hour.Offset)

/--
info: -86399999999999
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) - (1 : Day.Offset)

/--
info: -604799999999999
-/
#guard_msgs in
#eval (1 : Nanosecond.Offset) - (1 : Week.Offset)

/--
info: 999999
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) - (1 : Nanosecond.Offset)

/--
info: 0
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) - (1 : Millisecond.Offset)

/--
info: -999
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) - (1 : Second.Offset)

/--
info: -59999
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) - (1 : Minute.Offset)

/--
info: -3599999
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) - (1 : Hour.Offset)

/--
info: -86399999
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) - (1 : Day.Offset)

/--
info: -604799999
-/
#guard_msgs in
#eval (1 : Millisecond.Offset) - (1 : Week.Offset)

/--
info: 999999999
-/
#guard_msgs in
#eval (1 : Second.Offset) - (1 : Nanosecond.Offset)

/--
info: 999
-/
#guard_msgs in
#eval (1 : Second.Offset) - (1 : Millisecond.Offset)

/--
info: 0
-/
#guard_msgs in
#eval (1 : Second.Offset) - (1 : Second.Offset)

/--
info: -59
-/
#guard_msgs in
#eval (1 : Second.Offset) - (1 : Minute.Offset)

/--
info: -3599
-/
#guard_msgs in
#eval (1 : Second.Offset) - (1 : Hour.Offset)

/--
info: -86399
-/
#guard_msgs in
#eval (1 : Second.Offset) - (1 : Day.Offset)

/--
info: -604799
-/
#guard_msgs in
#eval (1 : Second.Offset) - (1 : Week.Offset)

/--
info: 59999999999
-/
#guard_msgs in
#eval (1 : Minute.Offset) - (1 : Nanosecond.Offset)

/--
info: 59999
-/
#guard_msgs in
#eval (1 : Minute.Offset) - (1 : Millisecond.Offset)

/--
info: 59
-/
#guard_msgs in
#eval (1 : Minute.Offset) - (1 : Second.Offset)

/--
info: 0
-/
#guard_msgs in
#eval (1 : Minute.Offset) - (1 : Minute.Offset)

/--
info: -59
-/
#guard_msgs in
#eval (1 : Minute.Offset) - (1 : Hour.Offset)

/--
info: -1439
-/
#guard_msgs in
#eval (1 : Minute.Offset) - (1 : Day.Offset)

/--
info: -10079
-/
#guard_msgs in
#eval (1 : Minute.Offset) - (1 : Week.Offset)

/--
info: 3599999999999
-/
#guard_msgs in
#eval (1 : Hour.Offset) - (1 : Nanosecond.Offset)

/--
info: 3599999
-/
#guard_msgs in
#eval (1 : Hour.Offset) - (1 : Millisecond.Offset)

/--
info: 3599
-/
#guard_msgs in
#eval (1 : Hour.Offset) - (1 : Second.Offset)

/--
info: 59
-/
#guard_msgs in
#eval (1 : Hour.Offset) - (1 : Minute.Offset)

/--
info: 0
-/
#guard_msgs in
#eval (1 : Hour.Offset) - (1 : Hour.Offset)

/--
info: -23
-/
#guard_msgs in
#eval (1 : Hour.Offset) - (1 : Day.Offset)

/--
info: -167
-/
#guard_msgs in
#eval (1 : Hour.Offset) - (1 : Week.Offset)

/--
info: 86399999999999
-/
#guard_msgs in
#eval (1 : Day.Offset) - (1 : Nanosecond.Offset)

/--
info: 86399999
-/
#guard_msgs in
#eval (1 : Day.Offset) - (1 : Millisecond.Offset)

/--
info: 86399
-/
#guard_msgs in
#eval (1 : Day.Offset) - (1 : Second.Offset)

/--
info: 1439
-/
#guard_msgs in
#eval (1 : Day.Offset) - (1 : Minute.Offset)

/--
info: 23
-/
#guard_msgs in
#eval (1 : Day.Offset) - (1 : Hour.Offset)

/--
info: 0
-/
#guard_msgs in
#eval (1 : Day.Offset) - (1 : Day.Offset)

/--
info: -6
-/
#guard_msgs in
#eval (1 : Day.Offset) - (1 : Week.Offset)

/--
info: 604799999999999
-/
#guard_msgs in
#eval (1 : Week.Offset) - (1 : Nanosecond.Offset)

/--
info: 604799999
-/
#guard_msgs in
#eval (1 : Week.Offset) - (1 : Millisecond.Offset)

/--
info: 604799
-/
#guard_msgs in
#eval (1 : Week.Offset) - (1 : Second.Offset)

/--
info: 10079
-/
#guard_msgs in
#eval (1 : Week.Offset) - (1 : Minute.Offset)

/--
info: 167
-/
#guard_msgs in
#eval (1 : Week.Offset) - (1 : Hour.Offset)

/--
info: 6
-/
#guard_msgs in
#eval (1 : Week.Offset) - (1 : Day.Offset)

/--
info: 0
-/
#guard_msgs in
#eval (1 : Week.Offset) - (1 : Week.Offset)
